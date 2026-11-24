---- MODULE EtcdBinding ----
\* Trace spec: each report of ../rawnode/node.go bound to EtcdRaft actions,
\* following the conventions of ../tracekit/tla/TraceKit.tla. Reports:
\*   boot    what a node recovered from disk           (Restart, undo)
\*   recv    the message the next reports answer       (checks the request)
\*   ready   raft's step for one input, in memory, and its write made first
\*                                                     (InMemory, then OnDisk)
\*   mem     the same with the write made later (AsyncStorageWrites, or a
\*           leader sending while it writes)           (InMemory; write queued)
\*   write   the oldest queued `mem` write, announced  (OnDisk)
\*   wrote   that write is done
\*   flush   batching: the oldest queued `mem` joins the next write (OnDisk)
\*   net     that whole write, announced (checked against the flushed reports)
\*   made    that write is on disk
\*   send    one message                               (GrantVote, Ack, ...)
\*   apply   entries handed to the state machine       (Apply)
\*   readreq / read   a read index asked for / given   (checked, ReadGiven)
\*   snap    a snapshot replaces the start of the log  (no model action)
\*   restore state machine replaced by a leader's snapshot (Restore)
\*   conf    a membership change applied               (SwitchConf)
\*
\* A node handles one input at a time, so each report is one determined
\* sequence of model actions, one step here; nothing is searched for.
\* Model node variables are the disk: in-memory reports bind to InMemory
\* (roles, BecomeLeader, LeaderAppend, LeaderCommit), writes to OnDisk
\* (StartElection, AdoptTerm, CastVote, DeleteSuffix, StoreEntries, Ack,
\* FollowerCommit). Writes not yet made wait in `queue`, in order.
\*
\* A batching node's `mem` has no `entries` (raft shows what a follower stored
\* only in the Ready): the follower stores what the model's follower would
\* (OnDisk, `takes`), and `net` checks the result against the write raft
\* asked for. Its messages are sent after several inputs, so a vote, ack or
\* vote request is checked to be a fact of its write and sent with that
\* write on disk (`made`).
\*
\* Server names are the node names and Nil is "", so reported values compare
\* directly with model values.
EXTENDS EtcdRaft, TraceKit, TLC, Integers

\* TRUE: nodes start with one entry (index 1, term 1) written by the service
\* (BootInit). FALSE: the model's Init.
CONSTANT Bootstrapped

VARIABLES
    i,        \* index of the next event
    undo,     \* per node: how to take back its last announced write
    pending,  \* per node: the message it is handling, as reported
    queue,    \* per node: the `mem` reports whose writes are still to come
    reads,    \* per node: the read indexes asked for and not given yet
    \* Safety checked per step (commits/applied are too large to keep): the
    \* longest committed prefix, its length per leader term, broken properties.
    chain, termLen, viol

tvars == <<vars, i, undo, pending, queue, reads, chain, termLen, viol>>

MaxReads == 16       \* reads remembered per node

GCBatch == 32        \* forget facts only this many at a time

----
\* Facts as the model writes them, from reported messages.

VoteFact(m) ==
    [type |-> "vote", src |-> m.from, term |-> m.term,
     lastLogIndex |-> m.index, lastLogTerm |-> m.logTerm]

\* A heartbeat is reported with index and log term 0.
AppendFact(m) ==
    [type |-> "append", src |-> m.from, dst |-> m.to, term |-> m.term,
     prevLogIndex |-> m.index, prevLogTerm |-> m.logTerm,
     entries |-> m.entries, commit |-> m.commit]

AckFact(src, dst, t, k) == [type |-> "ack", src |-> src, dst |-> dst, term |-> t, index |-> k]

IsReq(m) == m.type \in {"app", "hb", "snap"}

\* A snapshot sent is reported with its last index and term; in the model it
\* is a request with no previous entry carrying the committed first `index`
\* entries of the leader log (model logs are whole logs).
SnapOk(ll, m) ==
    m.type = "snap" =>
        /\ m.term \in DOMAIN ll /\ m.index <= Len(ll[m.term])
        /\ TermAt(ll[m.term], m.index) = m.logTerm

ReqFactIn(ll, m) ==
    IF m.type = "snap"
    THEN [type |-> "append", src |-> m.from, dst |-> m.to, term |-> m.term,
          prevLogIndex |-> 0, prevLogTerm |-> 0,
          entries |-> IF m.term \in DOMAIN ll THEN SubSeq(ll[m.term], 1, m.index) ELSE <<>>,
          commit |-> m.index]
    ELSE AppendFact(m)

ReqFact(m) == ReqFactIn(ledLog, m)

\* A bootstrapped cluster starts in term 1 with no vote on disk (BootInit).
BootTerm == IF Bootstrapped THEN 1 ELSE 0

\* HardState.Vote: the candidate voted for in the current term, if any.
VoteOf(vt, vf, t) == IF vt = t /\ t > BootTerm THEN vf ELSE Nil
Vote(n) == VoteOf(voteTerm[n], voteFor[n], currentTerm[n])

----
\* Committed prefixes: instead of `commits`, the longest seen (chain) and per
\* term the longest recorded under it (termLen); all are prefixes of chain
\* while CommitSafety holds. Passed as arguments because `ready` uses the
\* values after its in-memory part.

\* The model's CommittedIn.
RecordedIn(ch, tl, l, c, t) ==
    /\ c <= Len(l) /\ c <= Len(ch)
    /\ \E x \in DOMAIN tl : x <= t /\ tl[x] >= c
    /\ SubSeq(ch, 1, c) = SubSeq(l, 1, c)

\* The guard of the model's SendAppend for request f. Requests are never kept
\* as facts: SendAppend ignores the sender's state, so each use of a request
\* treats it as sent there and then.
SendableIn(ld, ll, ch, tl, f) ==
    /\ [server |-> f.src, term |-> f.term] \in ld
    /\ f.term \in DOMAIN ll
    /\ LET l == ll[f.term]
           p == f.prevLogIndex
           k == Len(f.entries)
       IN /\ p + k <= Len(l)
          /\ f.prevLogTerm = TermAt(l, p)
          /\ f.entries = SubSeq(l, p + 1, p + k)
          /\ f.commit = 0 \/ RecordedIn(ch, tl, l, f.commit, f.term)

Sendable(f) == SendableIn(leaders, ledLog, chain, termLen, f)

Comparable(a, b) == IsPrefix(a, b) \/ IsPrefix(b, a)

Matching(a, b) ==
    \A k \in 1..Min(Len(a), Len(b)) :
        a[k].term = b[k].term => a[k] = b[k] /\ (k > 1 => a[k-1].term = b[k-1].term)

LedWith(ll, t, l) == [u \in DOMAIN ll \cup {t} |-> IF u = t THEN l ELSE ll[u]]

\* Node n's in-memory commit index: of its last unwritten report, else disk.
MemCommit(n) == IF queue[n] = <<>> THEN commitIndex[n] ELSE queue[n][Len(queue[n])].ev.commit

\* The voters a report names are those of configuration C.
SameConf(ev, C) ==
    "voters" \in DOMAIN ev => Range(ev.voters) = C.in /\ Range(ev.outgoing) = C.out

----
\* Announced writes (TraceKit convention 3): atomic, so after a restart a
\* node has all or none of its last announced write. The pre-image (undo)
\* holds what is needed to take it back.

\* The term a node is in, or may be in after a restart; facts are kept while
\* some node may still need them.
EffTerm(j) == IF undo[j] = NoWrite THEN currentTerm[j] ELSE Min(currentTerm[j], undo[j][1].term)
Over(t) == \A j \in Server : EffTerm(j) > t

Recovered(ev, t, v, c, l) ==
    /\ ev.term = t /\ ev.vote = v /\ ev.commit = c
    /\ ev.lastIndex = Len(l) /\ ev.lastTerm = TermAt(l, Len(l))

\* boot: Restart, after taking back the last announced write if the recovered
\* state says it was not made. Unwritten memory is lost; what the node did as
\* a leader (leader log, commits) stays.
Boot(n, ev) ==
    /\ undo' = [undo EXCEPT ![n] = NoWrite]
    /\ pending' = [pending EXCEPT ![n] = <<>>]
    /\ queue' = [queue EXCEPT ![n] = <<>>]
    /\ reads' = [reads EXCEPT ![n] = <<>>]
    /\ role' = [role EXCEPT ![n] = Follower]
    /\ UNCHANGED <<leaders, ledLog, ledConf, ledAt, elAt, commits, applied, chain, termLen, viol>>
    /\ IF Recovered(ev, currentTerm[n], Vote(n), commitIndex[n], log[n])
       THEN UNCHANGED <<currentTerm, voteTerm, voteFor, log, commitIndex, confirmed, msgs, votes>>
       ELSE /\ undo[n] # NoWrite
            /\ LET u == undo[n][1]
                   l == SubSeq(log[n], 1, u.keep) \o u.suffix
               IN /\ ~u.made
                  /\ Recovered(ev, u.term, VoteOf(u.voteTerm, u.voteFor, u.term), u.commit, l)
                  /\ currentTerm' = [currentTerm EXCEPT ![n] = u.term]
                  /\ voteTerm' = [voteTerm EXCEPT ![n] = u.voteTerm]
                  /\ voteFor' = [voteFor EXCEPT ![n] = u.voteFor]
                  /\ commitIndex' = [commitIndex EXCEPT ![n] = u.commit]
                  /\ log' = [log EXCEPT ![n] = l]
                  /\ confirmed' = [confirmed EXCEPT ![n] = u.confirmed]
                  /\ msgs' = msgs \ u.msgs
                  /\ votes' = votes \ u.votes
    \* The state machine starts from the snapshot (Restore) or empty, raft
    \* with the configuration as of there.
    /\ LET a == IF "applied" \in DOMAIN ev THEN ev.applied ELSE 0
           C == ConfOf(log'[n], a)   \* RestoreConf: of the committed prefix checked next
       IN
       /\ a = 0 \/ /\ a <= Len(log'[n]) /\ a <= Len(chain)
                    /\ SubSeq(chain, 1, a) = SubSeq(log'[n], 1, a)
       /\ lastApplied' = [lastApplied EXCEPT ![n] = a]
       /\ config' = [config EXCEPT ![n] = C]
       /\ confAt' = [confAt EXCEPT ![n] = LastConf(log'[n], a)]
       /\ SameConf(ev, C)

----
\* recv: n starts handling a message. A request is checked against its
\* term's leader log (it may be a duplicate or delivered late).
Recv(n, ev) ==
    LET m == ev.msg IN
    /\ m.to = n
    /\ pending' = [pending EXCEPT ![n] = <<m>>]
    /\ IsReq(m) /\ m.term >= currentTerm[n] => SnapOk(ledLog, m) /\ Sendable(ReqFact(m))
    /\ UNCHANGED <<vars, undo, queue, reads, chain, termLen, viol>>

----
\* What a `ready`/`mem` report did in memory, as new variable values (`ok`:
\* the model allows it), in model order: role (BecomeCandidate,
\* BecomeFollower, BecomeLeader, which needs the campaign write on disk),
\* entries (LeaderAppend), commit (LeaderCommit, when a leader's commit index
\* first covers an entry of its term). A non-leader's memory is bound when
\* written.
InMemory(n, ev) ==
    LET T     == ev.term
        \* A pre-candidate has changed nothing: a follower in the model.
        role1 == IF ev.role = "precandidate" THEN Follower ELSE ev.role
        leads == ev.role = Leader
        wins  == leads /\ role[n] # Leader
        es    == IF "entries" \in DOMAIN ev THEN ev.entries ELSE <<>>
        ld1   == IF wins THEN leaders \cup {[server |-> n, term |-> T]} ELSE leaders
        ll1   == IF wins THEN LedWith(ledLog, T, log[n]) ELSE ledLog
        lc1   == IF wins THEN WithConf(T, config[n]) ELSE ledConf
        snapsM == "snap" \in DOMAIN ev
        known == IF T \in DOMAIN termLen THEN termLen[T] ELSE 0
        app   == leads /\ es # <<>>
        ll2   == IF app /\ T \in DOMAIN ll1 THEN LedWith(ll1, T, ll1[T] \o es) ELSE ll1
        L     == IF T \in DOMAIN ll2 THEN ll2[T] ELSE <<>>
        c     == ev.commit
        cmt   == leads /\ c > known /\ TermAt(L, c) = T
        newC  == SubSeq(L, 1, c)
    IN [ok |->
          /\ ev.by \in {"recv", "tick", "campaign", "propose", "write", "apply", "boot",
                       "transfer", "snapstatus", "read"}
          /\ ev.role \in {Follower, Candidate, Leader, "precandidate"}
          /\ snapsM => ev.role # Leader /\ role[n] # Leader /\ ev.snap.index <= Len(chain)
          /\ wins => /\ role[n] = Candidate /\ currentTerm[n] = T
                     /\ T \notin DOMAIN ledLog
                     /\ IsQuorum(Granted(n), config[n])
                     /\ OneWaiting(n, log[n])
                     \* CommittedBefore, with chain/termLen.
                     /\ confAt[n] = 0 \/ RecordedIn(chain, termLen, log[n], confAt[n], T - 1)
          /\ leads => /\ currentTerm[n] = T /\ T \in DOMAIN ll1
                      /\ c <= Len(L)
          /\ app => /\ "first" \in DOMAIN ev => ev.first = Len(ll1[T]) + 1
                    /\ \A q \in 1..Len(es) : es[q].term = T
                    \* A change of membership (LeaderAppend).
                    /\ \A q \in 1..Len(es) : IsConf(es[q]) =>
                          /\ AllSwitched(n, ll1[T])
                          /\ \A r \in 1..(q - 1) : ~IsConf(es[r])
                          /\ Legal(config[n], es[q].value)
          /\ leads /\ c > 0 =>
                IF cmt THEN IsQuorum(Acked(n, T, c), lc1[T])
                ELSE RecordedIn(chain, termLen, L, c, T),
        role |-> [role EXCEPT ![n] = role1],
        leaders |-> ld1,
        ledLog |-> ll2,
        ledConf |-> lc1,
        \* A snapshot from a leader: raft takes its configuration at once (RestoreConf).
        config |-> IF snapsM THEN [config EXCEPT ![n] = ConfOf(chain, ev.snap.index)] ELSE config,
        confAt |-> IF snapsM THEN [confAt EXCEPT ![n] = LastConf(chain, ev.snap.index)] ELSE confAt,
        ledAt |-> IF wins THEN With(ledAt, T, confAt[n]) ELSE ledAt,
        elAt |-> IF wins THEN With(elAt, T, confAt[n]) ELSE elAt,
        chain |-> IF cmt /\ c > Len(chain) THEN newC ELSE chain,
        termLen |-> IF cmt THEN [x \in DOMAIN termLen \cup {T} |-> IF x = T THEN c ELSE termLen[x]]
                    ELSE termLen,
        viol |-> viol
            \cup (IF cmt /\ ~Comparable(chain, newC) THEN {"CommitSafety"} ELSE {})
            \cup (IF \/ cmt /\ \E t \in DOMAIN ll2 : t > T /\ ~IsPrefix(newC, ll2[t])
                     \/ wins /\ \E x \in DOMAIN termLen :
                                  x < T /\ ~IsPrefix(SubSeq(chain, 1, termLen[x]), log[n])
                  THEN {"LeaderCompleteness"} ELSE {})
            \* Not the model's: raft campaigns only as a voter of its own
            \* configuration (promotable).
            \cup (IF ev.role = Candidate /\ role[n] # Candidate /\ n \notin config[n].in \cup config[n].out
                  THEN {"Unpromotable"} ELSE {})]

\* The write of report q = [ev, m] (m: the message being handled, if any),
\* given roles, leaders, leader logs and commits as they are then. In model
\* order: term (StartElection with the self-vote, or AdoptTerm), vote
\* (CastVote), entries (DeleteSuffix, StoreEntries for the request handled or
\* the leader's request to itself, then the leader's own Ack), commit
\* (FollowerCommit, after the Ack that confirms the request). The role is put
\* back to the in-memory one, never leader.
\* No `entries`: a batching non-leader handling an append of its term does what
\* handleAppendEntries does: answer with its commit index (`below`, i.e.
\* AckCommitted) or store from the first missing entry and ack (`takes`).
\* `more`: one atomic write with the last announced write, not yet made.
Lowest(a, b) == IF a = 0 THEN b ELSE IF b = 0 THEN a ELSE Min(a, b)

OnDisk(n, q, more, ro, ld, ll, ch, tl, vi) ==
    LET w     == q.ev
        hasM  == q.m # <<>>
        m     == q.m[1]
        T0    == currentTerm[n]
        T1    == w.term
        \* New term as candidate only by an election: timeout, pre-vote quorum,
        \* or timeoutnow.
        elect == T1 # T0 /\ w.role = Candidate
        adopt == T1 # T0 /\ ~elect
        V1    == IF T1 # T0 THEN Nil ELSE Vote(n)
        voted == w.vote # V1
        L0    == log[n]
        leads == w.role = Leader
        moved == w.commit # commitIndex[n]
        \* The request the node was handling.
        fm    == ReqFactIn(ll, m)
        \* A snapshot write: the entries it stands for are stored from the
        \* first one the log lacks.
        snaps == "snap" \in DOMAIN w
        bat   == "entries" \notin DOMAIN w
        isApp == bat /\ hasM /\ m.type = "app" /\ m.term = T1
        below == isApp /\ fm.prevLogIndex < commitIndex[n]
        takes == isApp /\ ~below /\ PrevOk(n, fm)
        Diff  == {x \in 1..Len(fm.entries) :
                     LET y == fm.prevLogIndex + x IN y > Len(L0) \/ L0[y].term # fm.entries[x].term}
        K     == IF Diff = {} THEN Len(fm.entries) + 1 ELSE CHOOSE x \in Diff : \A y \in Diff : x <= y
        es    == IF snaps \/ takes THEN SubSeq(fm.entries, K, Len(fm.entries))
                 ELSE IF bat THEN <<>> ELSE w.entries
        first == IF snaps \/ takes THEN fm.prevLogIndex + K
                 ELSE IF "first" \in DOMAIN w THEN w.first ELSE Len(L0) + 1
        stores == es # <<>>
        \* The request whose entries and commit index are written: the one
        \* handled, or the leader's own to itself.
        f     == IF leads
                 THEN [type |-> "append", src |-> n, dst |-> n, term |-> T1,
                       prevLogIndex |-> IF stores THEN first - 1 ELSE 0,
                       prevLogTerm |-> IF stores /\ T1 \in DOMAIN ll THEN TermAt(ll[T1], first - 1) ELSE 0,
                       entries |-> es, commit |-> IF moved THEN w.commit ELSE 0]
                 ELSE fm
        k     == first - f.prevLogIndex
        L1    == IF stores THEN SubSeq(L0, 1, first - 1) \o es ELSE L0
        last  == f.prevLogIndex + Len(f.entries)
        \* A leader acks what it stored to itself. A follower's ack is its
        \* reply (Send), except it acks the handled request before committing on it.
        acks  == \/ stores /\ leads
                 \/ moved /\ ~leads /\ hasM /\ m.type \in {"app", "snap"}
                 \/ takes \/ below
        \* AckCommitted: the commit index, and nothing confirmed.
        ackAt == IF below THEN commitIndex[n] ELSE last
        conf1 == IF stores THEN [term |-> T1, index |-> last]
                 ELSE IF acks /\ ~below THEN [term |-> T1, index |-> IF confirmed[n].term = T1
                                                           THEN Max(confirmed[n].index, last) ELSE last]
                 ELSE confirmed[n]
        req   == VoteRequest(n, T1)
        adv   == w.commit > commitIndex[n]
        newC  == SubSeq(L1, 1, w.commit)
        ch1   == IF adv /\ Len(newC) > Len(ch) THEN newC ELSE ch
        old   == IF T1 \in DOMAIN tl THEN tl[T1] ELSE 0
        pre   == [term |-> T0, voteTerm |-> voteTerm[n], voteFor |-> voteFor[n], commit |-> commitIndex[n],
                  keep |-> IF stores THEN first - 1 ELSE Len(L0),
                  suffix |-> IF stores THEN SubSeq(L0, first, Len(L0)) ELSE <<>>,
                  confirmed |-> confirmed[n],
                  msgs |-> msgs' \ msgs, votes |-> votes' \ votes,
                  \* The acks it makes, new facts or not.
                  acks |-> IF acks THEN {AckFact(n, f.src, T1, ackAt)} ELSE {},
                  \* The lowest index written since the last `net`.
                  low |-> IF stores THEN first ELSE 0,
                  \* Said to be on disk (`made`).
                  made |-> FALSE]
    IN
    /\ more => undo[n] # NoWrite
    /\ isApp => SendableIn(ld, ll, ch, tl, fm)
    \* The term.
    /\ T1 >= T0
    /\ T1 # T0 => ro[n] # Leader
    /\ elect => T1 = T0 + 1 /\ w.vote = n
    /\ adopt => /\ hasM /\ m.term = T1
                /\ \E j \in Server \ {n} : currentTerm[j] >= T1
    \* The vote.
    /\ voted => /\ V1 = Nil
                /\ elect \/ /\ hasM /\ m.type = "vote" /\ m.from = w.vote /\ m.term = T1
                            /\ VoteFact(m) \in msgs /\ UpToDate(VoteFact(m), n)
    \* The entries.
    /\ snaps => /\ ~leads /\ hasM /\ m.type = "snap" /\ stores
                /\ w.snap.index = m.index /\ w.snap.term = m.logTerm /\ w.commit = m.index
    /\ stores =>
          IF leads
          THEN /\ T1 = T0 /\ first = Len(L0) + 1
               /\ SendableIn(ld, ll, ch, tl, f)
          ELSE /\ hasM /\ m.type \in {"app", "snap"} /\ m.term = T1
               /\ m.type = "snap" => snaps
               /\ SnapOk(ll, m) /\ SendableIn(ld, ll, ch, tl, f)
               /\ PrevOk(n, f)
               /\ k \in 1..Len(f.entries)
               /\ HasFirst(n, f, k - 1)
               /\ es = SubSeq(f.entries, k, Len(f.entries))
               /\ IF first <= Len(L0) THEN L0[first].term # es[1].term
                  ELSE first = Len(L0) + 1
    \* The commit index.
    /\ moved =>
          /\ w.commit > commitIndex[n] /\ w.commit <= Len(L1)
          /\ IF leads
             THEN /\ T1 = T0 /\ SendableIn(ld, ll, ch, tl, f)
             ELSE /\ hasM /\ IsReq(m) /\ m.term = T1
                  /\ SnapOk(ll, m) /\ SendableIn(ld, ll, ch, tl, f)
                  /\ w.commit <= f.commit
                  /\ m.type \in {"app", "snap"} =>
                        PrevOk(n, f) /\ (stores \/ HasFirst(n, f, Len(f.entries)))
    /\ currentTerm' = [currentTerm EXCEPT ![n] = T1]
    /\ voteTerm' = [voteTerm EXCEPT ![n] = IF voted THEN T1 ELSE @]
    /\ voteFor' = [voteFor EXCEPT ![n] = IF voted THEN w.vote ELSE @]
    /\ log' = [log EXCEPT ![n] = L1]
    /\ commitIndex' = [commitIndex EXCEPT ![n] = w.commit]
    /\ role' = ro
    /\ confirmed' = [confirmed EXCEPT ![n] = conf1]
    /\ msgs' = msgs \cup (IF elect THEN {req} ELSE {})
                    \cup (IF acks THEN {AckFact(n, f.src, T1, ackAt)} ELSE {})
    /\ votes' = votes \cup (IF voted THEN {[voter |-> n, term |-> T1, cand |-> w.vote]} ELSE {})
    /\ leaders' = ld
    /\ ledLog' = ll
    /\ UNCHANGED <<lastApplied, commits, applied>>
    \* With `more`, the undo of both writes: older pre-image, log before it.
    /\ undo' = [undo EXCEPT ![n] = LastWrite(
          IF ~more THEN pre
          ELSE LET u == undo[n][1] IN
               [u EXCEPT !.keep = Min(u.keep, pre.keep),
                         !.suffix = IF pre.keep >= u.keep THEN u.suffix
                                    ELSE SubSeq(L0, pre.keep + 1, u.keep) \o u.suffix,
                         !.msgs = u.msgs \cup pre.msgs, !.votes = u.votes \cup pre.votes,
                         !.acks = u.acks \cup pre.acks,
                         !.low = Lowest(u.low, pre.low)])]
    \* Safety. A commit is recorded under the term of its request.
    /\ chain' = ch1
    /\ termLen' = IF adv THEN [x \in DOMAIN tl \cup {T1} |-> IF x = T1 THEN Max(old, Len(newC)) ELSE tl[x]]
                  ELSE tl
    /\ viol' = vi
         \cup (IF adv /\ ~Comparable(ch, newC) THEN {"CommitSafety"} ELSE {})
         \cup (IF adv /\ \E t \in DOMAIN ll : t > T1 /\ ~IsPrefix(newC, ll[t])
               THEN {"LeaderCompleteness"} ELSE {})
         \cup (IF L1 # L0 /\ \E b \in Server \ {n} : ~Matching(L1, log[b])
               THEN {"LogMatching"} ELSE {})
         \cup (IF (L1 # L0 \/ adv) /\ ~IsPrefix(SubSeq(ch1, 1, w.commit), L1)
               THEN {"CommittedEntriesPreserved"} ELSE {})
         \* The model commits within what the term's leader confirmed.
         \cup (IF adv /\ (conf1.term # T1 \/ w.commit > conf1.index)
               THEN {"CommitBeyondConfirmed"} ELSE {})

\* ready: what raft did in memory, and the write of it, at once.
Ready(n, ev) ==
    LET s == InMemory(n, ev)
        q == [ev |-> ev, m |-> IF ev.by = "recv" THEN pending[n] ELSE <<>>]
    IN /\ queue[n] = <<>>
       /\ s.ok
       /\ OnDisk(n, q, FALSE, s.role, s.leaders, s.ledLog, s.chain, s.termLen, s.viol)
       /\ ledConf' = s.ledConf /\ ledAt' = s.ledAt /\ elAt' = s.elAt
       /\ config' = s.config /\ confAt' = s.confAt
       /\ UNCHANGED <<pending, queue, reads>>

\* mem: what raft did in memory. A write that follows (ev.w = 1) is queued.
Mem(n, ev) ==
    LET s == InMemory(n, ev)
        q == [ev |-> ev, m |-> IF ev.by = "recv" THEN pending[n] ELSE <<>>]
    IN /\ s.ok
       /\ role' = s.role /\ leaders' = s.leaders /\ ledLog' = s.ledLog
       /\ ledConf' = s.ledConf /\ ledAt' = s.ledAt /\ elAt' = s.elAt
       /\ config' = s.config /\ confAt' = s.confAt
       /\ chain' = s.chain /\ termLen' = s.termLen /\ viol' = s.viol
       /\ queue' = [queue EXCEPT ![n] = IF ev.w = 1 THEN Append(@, q) ELSE @]
       /\ UNCHANGED <<durable, lastApplied, confirmed, msgs, votes, commits, applied, undo, pending, reads>>

\* write: the oldest queued report of n is written.
Write(n, ev) ==
    /\ queue[n] # <<>>
    /\ LET q == Head(queue[n])
           w == q.ev
       IN /\ ev.term = w.term /\ ev.vote = w.vote /\ ev.commit = w.commit
          /\ ev.first = w.first /\ ev.entries = w.entries
          /\ OnDisk(n, q, FALSE, role, leaders, ledLog, chain, termLen, viol)
    /\ queue' = [queue EXCEPT ![n] = Tail(@)]
    /\ UNCHANGED <<config, confAt, ledConf, ledAt, elAt, pending, reads>>

\* flush: the oldest queued report joins the next write; more = 1: the same
\* write as the previous flush.
Flush(n, ev) ==
    /\ queue[n] # <<>>
    /\ OnDisk(n, Head(queue[n]), ev.more = 1, role, leaders, ledLog, chain, termLen, viol)
    /\ queue' = [queue EXCEPT ![n] = Tail(@)]
    /\ UNCHANGED <<config, confAt, ledConf, ledAt, elAt, pending, reads>>

\* net: the write raft asked for. The reports flushed since the last `net`
\* left exactly its term, vote and commit index, and a log changed only from
\* its first entry on, holding its entries (or unchanged).
Net(n, ev) ==
    /\ undo[n] # NoWrite
    /\ LET u == undo[n][1] IN
       /\ ev.term = currentTerm[n] /\ ev.vote = Vote(n) /\ ev.commit = commitIndex[n]
       /\ IF ev.entries = <<>> THEN u.low = 0
          ELSE /\ u.low = ev.first
               /\ Len(log[n]) = ev.first + Len(ev.entries) - 1
               /\ SubSeq(log[n], ev.first, Len(log[n])) = ev.entries
       /\ undo' = [undo EXCEPT ![n] = LastWrite([u EXCEPT !.low = 0])]
    /\ UNCHANGED <<vars, pending, queue, reads, chain, termLen, viol>>

\* made: n's last announced write is on disk and cannot be taken back; its
\* facts stay until `wrote` for the messages that state them.
Made(n, ev) ==
    /\ undo[n] # NoWrite
    /\ undo' = [undo EXCEPT ![n] = LastWrite([@[1] EXCEPT !.made = TRUE])]
    /\ UNCHANGED <<vars, pending, queue, reads, chain, termLen, viol>>

\* wrote: node n's last announced write is made.
Wrote(n, ev) ==
    /\ undo' = [undo EXCEPT ![n] = NoWrite]
    /\ UNCHANGED <<vars, pending, queue, reads, chain, termLen, viol>>

----
\* send: one message from n. A vote, ack or vote request is sent after the
\* write it depends on. With later writes, a message names the message it
\* answers (`cause`) and others do not wait for a write.
Send(n, ev) ==
    LET s    == ev.msg
        late == "cause" \in DOMAIN ev
        \* Batched Ready (several inputs): checked against the facts, including
        \* those of the last write, kept until `wrote`.
        bt   == "b" \in DOMAIN ev
        mine == IF bt /\ undo[n] # NoWrite THEN undo[n][1].msgs ELSE {}
        cast == IF bt /\ undo[n] # NoWrite THEN undo[n][1].votes ELSE {}
        \* No write of the node is announced and not on disk.
        dur  == IF undo[n] = NoWrite THEN TRUE ELSE undo[n][1].made
        C    == IF late THEN ev.cause ELSE pending[n]
    IN
    \* Forwarded as is, with another sender: readindex (by a follower),
    \* transfer (the transferee as sender), prop (by a non-leader).
    /\ s.from = n \/ s.type \in {"readindex", "transfer", "prop"}
    /\ s.to \in Server \ {n}
    \* Where writes are made later, `wrote` says when one is made.
    /\ undo' = [undo EXCEPT ![n] = IF late \/ bt THEN @ ELSE NoWrite]
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, commitIndex, role, lastApplied, config, confAt,
                   votes, leaders, ledLog, ledConf, ledAt, elAt, commits, applied, pending, queue, reads, chain, termLen, viol>>
    /\ CASE s.type = "vote" ->
              \* The request became a fact with the election's term write.
              /\ IF bt THEN dur /\ VoteFact(s) \in msgs \cup mine
                 ELSE s.term = currentTerm[n] /\ VoteFact(s) \in msgs
              /\ UNCHANGED <<msgs, confirmed>>
         [] s.type = "voteresp" ->
              \* GrantVote.
              /\ ~s.reject => /\ [voter |-> n, term |-> s.term, cand |-> s.to] \in votes \cup cast
                              /\ bt => dur
              /\ msgs' = IF s.reject THEN msgs
                         ELSE msgs \cup {[type |-> "grant", src |-> n, dst |-> s.to, term |-> s.term]}
              /\ UNCHANGED confirmed
         [] IsReq(s) ->
              \* SendAppend, from the in-memory leader log. (Batched: the
              \* node may have stepped down; SendAppend ignores the sender.)
              /\ bt \/ (s.term = currentTerm[n] /\ role[n] = Leader)
              /\ SnapOk(ledLog, s) /\ Sendable(ReqFact(s))
              /\ UNCHANGED <<msgs, confirmed>>
         [] s.type = "appresp" ->
              IF s.reject THEN UNCHANGED <<msgs, confirmed>>
              ELSE IF bt
              THEN \* An ack made by OnDisk for the last write, on disk; or none.
                   /\ \/ s.index = 0
                      \/ /\ undo[n] # NoWrite /\ dur
                         /\ AckFact(n, s.to, s.term, s.index) \in undo[n][1].acks
                   /\ UNCHANGED <<msgs, confirmed>>
              ELSE IF C # <<>> /\ IsReq(C[1]) /\ C[1].term < currentTerm[n]
              THEN \* PreVote/CheckQuorum: a request of an earlier term is answered
                   \* so the sender learns the term; acks nothing.
                   /\ s.index = 0 /\ s.term = currentTerm[n]
                   /\ UNCHANGED <<msgs, confirmed>>
              ELSE IF s.index = 0
              THEN \* Acks nothing: a node with commit index 0 refusing a
                   \* snapshot whose voters exclude it.
                   UNCHANGED <<msgs, confirmed>>
              ELSE /\ C # <<>>
                   /\ LET m == C[1]
                          f == ReqFact(m)
                          last == f.prevLogIndex + Len(f.entries)
                      IN /\ m.type \in {"app", "snap"} /\ SnapOk(ledLog, m) /\ Sendable(f)
                         /\ s.to = m.from /\ s.term = m.term /\ currentTerm[n] = m.term
                         /\ IF s.index = last /\ PrevOk(n, f) /\ HasFirst(n, f, Len(f.entries))
                            THEN \* Ack.
                                 /\ msgs' = msgs \cup {AckFact(n, m.from, m.term, last)}
                                 /\ confirmed' = [confirmed EXCEPT ![n] =
                                       [term |-> m.term,
                                        index |-> IF @.term = m.term THEN Max(@.index, last) ELSE last]]
                            ELSE \* AckCommitted.
                                 /\ f.prevLogIndex < commitIndex[n] /\ s.index = commitIndex[n]
                                 /\ msgs' = msgs \cup {AckFact(n, m.from, m.term, commitIndex[n])}
                                 /\ UNCHANGED confirmed
         [] s.type = "hbresp" ->
              \* Lets a leader give a read index (EtcdRaft ReadAck): the
              \* node's disk is not in a later term than the answer.
              /\ (IF bt THEN EffTerm(n) ELSE currentTerm[n]) <= s.term
              /\ UNCHANGED <<msgs, confirmed>>
         [] s.type \in {"prevote", "prevoteresp", "readindex", "readindexresp",
                        "prop", "transfer", "timeoutnow"} ->
              \* No model action: a pre-vote changes no state and its reply
              \* promises nothing; reads are checked in ReadGiven; a forwarded
              \* proposal counts when the leader appends it; timeoutnow leads
              \* to an ordinary election.
              UNCHANGED <<msgs, confirmed>>
         [] OTHER -> FALSE

----
\* apply: Apply for each entry in order (log up to there committed). Without
\* `a` the node applies after its write, so no write is in doubt.
ApplyEv(n, ev) ==
    LET last == ev.first + Len(ev.entries) - 1 IN
    /\ ev.first = lastApplied[n] + 1
    /\ last <= Len(log[n]) /\ last <= Len(chain)
    /\ SubSeq(chain, 1, last) = SubSeq(log[n], 1, last)
    /\ ev.entries = SubSeq(log[n], ev.first, last)
    /\ lastApplied' = [lastApplied EXCEPT ![n] = last]
    /\ undo' = [undo EXCEPT ![n] = IF "a" \in DOMAIN ev THEN @ ELSE NoWrite]
    \* Not the model's: raft applies within its in-memory commit index.
    /\ viol' = viol \cup (IF last > MemCommit(n) THEN {"ApplyBeyondCommit"} ELSE {})
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, commitIndex, role, config, confAt, confirmed, msgs,
                   votes, leaders, ledLog, ledConf, ledAt, elAt, commits, applied, pending, queue, reads, chain, termLen>>

----
\* conf: SwitchConf. The next change after confAt, applied and Legal; the
\* voters raft reports are the model's.
ConfEv(n, ev) ==
    LET k == ev.index IN
    /\ k > confAt[n] /\ k <= lastApplied[n] /\ k <= Len(log[n])
    /\ k <= Len(chain) /\ SubSeq(chain, 1, k) = SubSeq(log[n], 1, k)
    /\ IsConf(log[n][k])
    /\ \A q \in (confAt[n] + 1)..(k - 1) : ~IsConf(log[n][q])
    /\ Legal(config[n], log[n][k].value)
    \* A leader knows it to be committed under its own term or before.
    /\ role[n] = Leader => RecordedIn(chain, termLen, log[n], k, currentTerm[n])
    /\ LET C == NextConf(config[n], log[n][k].value) IN
       /\ SameConf(ev, C)
       /\ config' = [config EXCEPT ![n] = C]
       /\ ledConf' = IF role[n] = Leader THEN WithConf(currentTerm[n], C) ELSE ledConf
    /\ ledAt' = IF role[n] = Leader THEN With(ledAt, currentTerm[n], k) ELSE ledAt
    /\ confAt' = [confAt EXCEPT ![n] = k]
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, commitIndex, role, lastApplied, confirmed, msgs,
                   votes, leaders, ledLog, elAt, commits, applied, undo, pending, queue, reads, chain, termLen, viol>>

----
\* restore: Restore with a leader's snapshot, already in the log and committed.
RestoreEv(n, ev) ==
    /\ ev.index <= Len(log[n]) /\ ev.index <= Len(chain)
    /\ SubSeq(chain, 1, ev.index) = SubSeq(log[n], 1, ev.index)
    /\ lastApplied' = [lastApplied EXCEPT ![n] = ev.index]
    \* Its configuration is the one its entries make (raft took it on
    \* arrival: InMemory).
    /\ SameConf(ev, ConfOf(chain, ev.index))
    /\ undo' = [undo EXCEPT ![n] = IF "a" \in DOMAIN ev THEN @ ELSE NoWrite]
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, commitIndex, role, config, confAt, confirmed, msgs,
                   votes, leaders, ledLog, ledConf, ledAt, elAt, commits, applied, pending, queue, reads, chain, termLen, viol>>

\* snap: no model action (model logs are whole). The index is applied and
\* within the commit index on disk.
SnapEv(n, ev) ==
    /\ ev.index <= lastApplied[n] /\ ev.index <= commitIndex[n]
    /\ TermAt(log[n], ev.index) = ev.term
    /\ UNCHANGED <<vars, undo, pending, queue, reads, chain, termLen, viol>>

----
\* Read index (raft's ReadIndex), checked without a model action: the index
\* given must cover every prefix committed, by any node, when the read was
\* asked for (linearizability). Only the last MaxReads requests per node are
\* remembered; an answer to an older one is not checked.
ReadAsked(n, ev) ==
    LET r == [ctx |-> ev.ctx, floor |-> Len(chain)]
        q == Append(reads[n], r)
    IN /\ reads' = [reads EXCEPT ![n] = IF Len(q) > MaxReads THEN Tail(q) ELSE q]
       /\ UNCHANGED <<vars, undo, pending, queue, chain, termLen, viol>>

ReadGiven(n, ev) ==
    LET S == {k \in 1..Len(reads[n]) : reads[n][k].ctx = ev.ctx} IN
    /\ reads' = [reads EXCEPT ![n] = SelectSeq(@, LAMBDA r : r.ctx # ev.ctx)]
    /\ viol' = viol \cup (IF \E k \in S : ev.index < reads[n][k].floor THEN {"ReadIndexStale"} ELSE {})
    /\ UNCHANGED <<vars, undo, pending, queue, chain, termLen>>

Bind(n, ev) ==
    CASE ev.e = "boot" -> Boot(n, ev)
      [] ev.e = "recv" -> Recv(n, ev)
      [] ev.e = "ready" -> Ready(n, ev)
      [] ev.e = "mem" -> Mem(n, ev)
      [] ev.e = "write" -> Write(n, ev)
      [] ev.e = "wrote" -> Wrote(n, ev)
      [] ev.e = "flush" -> Flush(n, ev)
      [] ev.e = "net" -> Net(n, ev)
      [] ev.e = "made" -> Made(n, ev)
      [] ev.e = "send" -> Send(n, ev)
      [] ev.e = "apply" -> ApplyEv(n, ev)
      [] ev.e = "restore" -> RestoreEv(n, ev)
      [] ev.e = "conf" -> ConfEv(n, ev)
      [] ev.e = "snap" -> SnapEv(n, ev)
      [] ev.e = "readreq" -> ReadAsked(n, ev)
      [] ev.e = "read" -> ReadGiven(n, ev)
      [] OTHER -> FALSE   \* includes Gap: the stream has a hole

----
\* Forgetting facts (TraceKit convention 4); every model guard is positive in
\* msgs, votes, leaders and ledLog. Dropped: vote requests of terms all nodes
\* left; grants and acks to a node past their term; acks covered by a later
\* one not of a write that may be taken back; votes of terms their voter
\* left; leaders and leader logs of terms all nodes left (such a term has no
\* candidate, so BecomeLeader's "no leader log yet" is unaffected).

Garbage ==
    {m \in msgs :
        CASE m.type = "vote" -> Over(m.term)
          [] m.type = "grant" -> EffTerm(m.dst) > m.term
          [] m.type = "ack" ->
               \/ EffTerm(m.dst) > m.term
               \/ \E a \in msgs : /\ a.type = "ack" /\ a.src = m.src /\ a.dst = m.dst
                                  /\ a.term = m.term /\ a.index > m.index
                                  \* and is not of a write that may be taken back
                                  /\ undo[a.src] = NoWrite \/ a \notin undo[a.src][1].msgs
          [] OTHER -> FALSE}

OldVotes == {v \in votes : EffTerm(v.voter) > v.term}
StaleLed == {t \in DOMAIN ledLog : Over(t)}

GCDue == Cardinality(Garbage) + Cardinality(OldVotes) >= GCBatch \/ StaleLed # {}

GC ==
    /\ GCDue
    /\ msgs' = msgs \ Garbage
    /\ votes' = votes \ OldVotes
    /\ ledLog' = [t \in DOMAIN ledLog \ StaleLed |-> ledLog[t]]
    /\ ledConf' = [t \in DOMAIN ledConf \ StaleLed |-> ledConf[t]]
    /\ ledAt' = [t \in DOMAIN ledAt \ StaleLed |-> ledAt[t]]
    /\ elAt' = [t \in DOMAIN elAt \ StaleLed |-> elAt[t]]
    /\ leaders' = {l \in leaders : ~Over(l.term)}
    /\ UNCHANGED <<currentTerm, voteTerm, voteFor, log, commitIndex, role, lastApplied, config, confAt, confirmed,
                   commits, applied, i, undo, pending, queue, reads, chain, termLen, viol>>

----
\* A cluster bootstrapped with one entry (index 1, term 1; Config.Boot in
\* ../rawnode/node.go) is the model after a first election in term 1: First
\* got every vote, led, appended the entry, every node stored it; nothing
\* acked or committed, First is a follower, and that term's facts are
\* forgotten. MCEtcd.tla has TLC reach this state from Init.
First == CHOOSE s \in InitVoters : TRUE

BootInit ==
    /\ currentTerm = [s \in Server |-> 1]
    /\ voteTerm    = [s \in Server |-> 1]
    /\ voteFor     = [s \in Server |-> First]
    /\ log         = [s \in Server |-> <<Entry(1, "config", Nil)>>]
    /\ role        = [s \in Server |-> Follower]
    /\ commitIndex = [s \in Server |-> 0]
    /\ lastApplied = [s \in Server |-> 0]
    /\ config      = [s \in Server |-> InitConf]
    /\ confAt      = [s \in Server |-> 0]
    /\ confirmed   = [s \in Server |-> [term |-> 1, index |-> 1]]
    /\ msgs        = {}
    /\ votes       = {}
    /\ leaders     = {[server |-> First, term |-> 1]}
    /\ ledLog      = (1 :> <<Entry(1, "config", Nil)>>)
    /\ ledConf     = (1 :> InitConf)
    /\ ledAt       = (1 :> 0)
    /\ elAt        = (1 :> 0)
    /\ commits     = {}
    /\ applied     = {}
    /\ read        = NoRead

Init0 ==
    /\ IF Bootstrapped THEN BootInit ELSE Init
    /\ i = 1
    /\ undo = [n \in Server |-> NoWrite]
    /\ pending = [n \in Server |-> <<>>]
    /\ queue = [n \in Server |-> <<>>]
    /\ reads = [n \in Server |-> <<>>]
    /\ chain = <<>>
    /\ termLen = <<>>
    /\ viol = {}

Step ==
    /\ ~GCDue
    /\ LET ev == StreamEvent(i)
           n  == ev.node
       IN /\ ev.e # "End"
          /\ Bind(n, ev)
    /\ i' = i + 1

\* The model's `read` is not followed: ReadGiven checks every read itself.
Next0 == (GC \/ Step) /\ UNCHANGED read
TraceSpec == Init0 /\ [][Next0]_<<tvars, read>>

\* No step broke CommitSafety, LeaderCompleteness, LogMatching,
\* CommittedEntriesPreserved, CommitBeyondConfirmed, ApplyBeyondCommit,
\* ReadIndexStale or Unpromotable (StateMachineSafety, TermMonotonic and
\* CommitMonotonic are conditions of the steps).
Safe == viol = {}

LogTail(l) == SubSeq(l, Max(1, Len(l) - 5), Len(l))

Alias ==
    [i |-> i, viol |-> viol, currentTerm |-> currentTerm, role |-> role,
     voteTerm |-> voteTerm, voteFor |-> voteFor, commitIndex |-> commitIndex, lastApplied |-> lastApplied,
     config |-> config, confAt |-> confAt, ledConf |-> ledConf,
     confirmed |-> confirmed, lastIndex |-> [n \in Server |-> Len(log[n])],
     logTail |-> [n \in Server |-> LogTail(log[n])],
     msgs |-> msgs, votes |-> votes, leaders |-> leaders, ledTerms |-> DOMAIN ledLog,
     pending |-> pending, undo |-> undo, termLen |-> termLen, chainLen |-> Len(chain),
     queue |-> [n \in Server |-> [k \in 1..Len(queue[n]) |-> queue[n][k].ev]]]
====
