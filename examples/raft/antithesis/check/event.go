package check

// Msg is a reported message, `{type, from, to, term, index, logTerm, entries, commit, reject, hint}`
// (antithesis-fm/rawnode/node.go's package comment). Every field is always reported.
//
// Has says which fields the report has (MF* bits): reading an absent one is an EvalError, as in
// TLC. A message the harness builds has them all (MFAll).
type Msg struct {
	Has     uint32
	Type    string
	From    string
	To      string
	Term    int
	Index   int
	LogTerm int
	Entries []Entry
	Commit  int
	Reject  bool
	Hint    int
}

// The fields of a reported message, as bits of Msg.Has.
const (
	MFType uint32 = 1 << iota
	MFFrom
	MFTo
	MFTerm
	MFIndex
	MFLogTerm
	MFEntries
	MFCommit
	MFReject
	MFAll = MFType | MFFrom | MFTo | MFTerm | MFIndex | MFLogTerm | MFEntries | MFCommit | MFReject
)

func (m Msg) need(f uint32) {
	if m.Has&f == 0 {
		evalError("a field the message does not have")
	}
}

func (m Msg) typ() string      { m.need(MFType); return m.Type }
func (m Msg) from() string     { m.need(MFFrom); return m.From }
func (m Msg) to() string       { m.need(MFTo); return m.To }
func (m Msg) term() int        { m.need(MFTerm); return m.Term }
func (m Msg) index() int       { m.need(MFIndex); return m.Index }
func (m Msg) logTerm() int     { m.need(MFLogTerm); return m.LogTerm }
func (m Msg) entries() []Entry { m.need(MFEntries); return m.Entries }
func (m Msg) commit() int      { m.need(MFCommit); return m.Commit }
func (m Msg) reject() bool     { m.need(MFReject); return m.Reject }

// SnapRef is a report's `snap`: `{index, term}`.
type SnapRef struct {
	Index int
	Term  int
}

// The fields a report may have besides `e` and `node`, as bits of Event.Has: `"f" \in DOMAIN ev`
// is ev.Has&F != 0. Reading an absent field is an EvalError, as in TLC.
const (
	FBy uint32 = 1 << iota
	FRole
	FTerm
	FVote
	FCommit
	FFirst
	FEntries
	FLastIndex
	FLastTerm
	FApplied
	FVoters
	FOutgoing
	FSnap
	FMsg
	FCause
	FB
	FA
	FW
	FMore
	FIndex
	FCtx
)

// Event is one report of the stream: TraceKit's StreamEvent(i) (antithesis-fm/tracekit/stream/
// TraceKit.java turns a JSON line into a TLA+ record). Fields the binding never reads (`k`,
// `seq`, `boot`, ...) are dropped. Bad, if not empty, says why the line is not a record of the
// shape the binding reads (a field of the wrong kind): processing it is an EvalError.
type Event struct {
	E        string
	Node     string
	Has      uint32
	By       string
	Role     string
	Term     int
	Vote     string
	Commit   int
	First    int
	Entries  []Entry
	LastIdx  int
	LastTerm int
	Applied  int
	Voters   []string
	Outgoing []string
	Snap     SnapRef
	Msg      Msg
	Cause    []Msg
	W        int
	More     int
	Index    int
	Ctx      string
	Bad      string
}

func (ev *Event) has(f uint32) bool { return ev.Has&f != 0 }

func (ev *Event) need(f uint32) {
	if ev.Has&f == 0 {
		evalError("a field the report does not have")
	}
}

func (ev *Event) by() string {
	ev.need(FBy)
	return ev.By
}

func (ev *Event) role() string {
	ev.need(FRole)
	return ev.Role
}

func (ev *Event) term() int {
	ev.need(FTerm)
	return ev.Term
}

func (ev *Event) vote() string {
	ev.need(FVote)
	return ev.Vote
}

func (ev *Event) commit() int {
	ev.need(FCommit)
	return ev.Commit
}

func (ev *Event) first() int {
	ev.need(FFirst)
	return ev.First
}

func (ev *Event) entries() []Entry {
	ev.need(FEntries)
	return ev.Entries
}

func (ev *Event) lastIndex() int {
	ev.need(FLastIndex)
	return ev.LastIdx
}

func (ev *Event) lastTerm() int {
	ev.need(FLastTerm)
	return ev.LastTerm
}

func (ev *Event) applied() int {
	ev.need(FApplied)
	return ev.Applied
}

func (ev *Event) voters() []string {
	ev.need(FVoters)
	return ev.Voters
}

func (ev *Event) outgoing() []string {
	ev.need(FOutgoing)
	return ev.Outgoing
}

func (ev *Event) snap() SnapRef {
	ev.need(FSnap)
	return ev.Snap
}

func (ev *Event) msg() Msg {
	ev.need(FMsg)
	return ev.Msg
}

func (ev *Event) cause() []Msg {
	ev.need(FCause)
	return ev.Cause
}

func (ev *Event) w() int {
	ev.need(FW)
	return ev.W
}

func (ev *Event) more() int {
	ev.need(FMore)
	return ev.More
}

func (ev *Event) index() int {
	ev.need(FIndex)
	return ev.Index
}

func (ev *Event) ctx() string {
	ev.need(FCtx)
	return ev.Ctx
}

// msgSeqHead is `C[1]` for a sequence C of messages: an EvalError on <<>>.
func msgSeqHead(c []Msg) Msg {
	if len(c) == 0 {
		evalError("<<>>[1]")
	}
	return c[0]
}
