/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Model/StepGryff.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The Gryff register handlers: the participant (`gryffcommon/participant.go`) and the coordinator
(`gryffcommon/coordinator.go`), with the replica's wrappers (`tupaq.go`: `handle*`, `Send*`,
`Complete*`, `reply*Replica`, `send*To`). Key 0 only (every other key is never produced).

`SendRead1`/`SendRead2`/`SendWrite1`/`SendWrite2` loop over their `replicas` in order; a send to
the replica itself goes to its own channel (`send*To`), to a peer by `SendMsg`: both are a message
to that replica (`sendTo`).
-/
module

public import Dsverify.Proof.gryff.Model.StepBase

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.model

/-! ## Participant -/

/-- `handleRead1Proxied` → `HandleRead1(K, &D, RequestId, ClientId, true, &Vt, ReplicaId)` →
`replyRead1Replica(ReplicaId, r1reply)`. -/
def stepRead1 (s : RState) (m : Read1ProxiedM) : StepRes := do
  if m.k ≠ 0 then never
  let mut s := s
  if sge m.d.key 0 then
    -- `SendRead1` never sets `D`: it is the zero `Dep` (key 0), and this overwrite never changes
    -- the store (tag (0,0,0)); kept as the code does it
    if m.d.key ≠ 0 then never
    s := s.overwrite m.d.vt.v m.d.vt.t
  s := s.overwrite m.vt.v m.vt.t
  let r : Read1ReplyM := { requestId := m.requestId, clientId := m.clientId, replicaId := s.id,
                           vt := s.storeVT }
  let some o := sendTo m.replicaId (.read1Reply r)
    | dead -- dead: ReplicaId is the coordinator's id (`SendRead1`)
  return (s, [o])

/-- `handleRead2Proxied` → `HandleRead2(K, Vt, ...)` → `replyRead2Replica(ReplicaId, ...)`. -/
def stepRead2 (s : RState) (m : Read2ProxiedM) : StepRes := do
  if m.k ≠ 0 then never
  let s := s.overwrite m.vt.v m.vt.t
  let some o := sendTo m.replicaId (.read2Reply { requestId := m.requestId, clientId := m.clientId })
    | dead -- dead: ReplicaId is the coordinator's id (`SendRead2`)
  return (s, [o])

/-- `handleWrite1Proxied` → `HandleWrite1(K, V, N, &D, RequestId, ClientId, &MaxAppliedTag,
ForceWrite, ReplicaId)` → (if a reply) `replyWrite1Replica(ReplicaId, w1reply)`. -/
def stepWrite1 (s : RState) (m : Write1ProxiedM) : StepRes := do
  if m.k ≠ 0 then never
  if let some r := s.ongoing.get? m.clientId then
    if sgt r m.requestId then
      return (s, [])
  let mut s := s
  if sge m.d.key 0 then
    if m.d.key ≠ 0 then never
    s := s.overwrite m.d.vt.v m.d.vt.t
  match s.ongoing.get? m.clientId with
  | some r =>
    if slt r m.requestId then
      s := { s with ongoing := s.ongoing.put m.clientId m.requestId }
  | none =>
    s := { s with ongoing := s.ongoing.put m.clientId m.requestId }
  -- `valTag := {V: -1, T: *meta.Tag}`
  if !(sgt m.forceWrite 0) then never -- every Write1 is forced (`StartWrite`: forceWrite = 1)
  -- the entry's `SentWrite1Reply = true` (implicit: see `RState.ongoing`)
  let r : Write1ReplyM := { requestId := m.requestId, clientId := m.clientId, vt := ⟨-1, s.tag⟩ }
  let some o := sendTo m.replicaId (.write1Reply r)
    | dead -- dead: ReplicaId is the coordinator's id (`SendWrite1`)
  return (s, [o])

/-- `handleWrite2Proxied` → `HandleWrite2(K, Vt, RequestId, ClientId)` →
`replyWrite2Replica(ReplicaId, w2reply)`. -/
def stepWrite2 (s : RState) (m : Write2ProxiedM) : StepRes := do
  if m.k ≠ 0 then never
  let applied : w32 := if s.tag.lt m.vt.t then 1 else 0
  let s := s.overwrite m.vt.v m.vt.t
  let s := { s with ongoing := s.ongoing.del m.clientId }
  -- the loop over `OngoingWrites`: every entry has `SentWrite1Reply = true`, so it only sets
  -- `ongoingWrite` (unread then: `concurrentWrites` stays empty); no effect
  let r : Write2ReplyM := { requestId := m.requestId, clientId := m.clientId, applied }
  let some o := sendTo m.replicaId (.write2Reply r)
    | dead -- dead: ReplicaId is the coordinator's id (`SendWrite2`)
  return (s, [o])

/-! ## Coordinator -/

/-- `GryffCoordinator.ShortCircuit(n, value, fastOverwrite)`: the reads to complete, in the
order of the sorted `ShortReads` of op `n`. `sort.Slice` sorts `OngoingReqs[n].ShortReads` in
place: the model writes the sorted list back at `n` (H1-R4; both callers delete `OngoingReqs[n]`
right after, so their results do not depend on it). Without `fastOverwrite` the code reads
`OngoingReqs[n].ShortWrites` after the reads loop: the model re-reads the entry (`dead` if the
loop deleted it, H1-R3: unreachable, `ShortReads` holds reads' numbers and `n` is a write's). The
`ShortWrites` loop iterates an empty list (see `OngoingOp`). -/
def shortCircuit (s : RState) (n : w32) (value : ValTag) (fastOverwrite : Bool) :
    Option (RState × List Out) := do
  let some op := s.ongoingReqs.get? n
    | dead -- dead: both callers hold op n's write, whose OngoingReqs entry is deleted with it
  let keys := op.shortReads.mergeSort (fun a b => sle a b)
  let mut s := { s with ongoingReqs := s.ongoingReqs.put n { op with shortReads := keys } }
  let mut outs : List Out := []
  for k in keys do
    if sge k n && fastOverwrite then break
    let some o := s.ongoingReqs.get? k | continue
    let id := shiftInts o.requestId o.clientId
    let some _read := s.rops.get? id | continue
    s := { s with ongoingReqs := s.ongoingReqs.del k, rops := s.rops.del id }
    outs := outs ++ [.ext (.readReply o.clientId o.requestId value.v 1)]
  if !fastOverwrite then
    let some _ := s.ongoingReqs.get? n
      | dead -- dead: `c.OngoingReqs[n].ShortWrites` (H1-R3); `n` is not among the reads deleted
  return (s, outs)

/-- The client's Read (`readChan` → `handleRead` → `StartRead(RequestId, ClientId, K, &D)`):
the event's guard is the system's shape (key 0, no dependency: `D.Key < 0`, Go's own test, a
client id ≥ 0), the budget and a fresh (client id, request id) at this replica (ghost:
`RState.used`). `D` is stored in the read op (`Op.Dep`) and never read again (`SendRead1` sends
the scratch `r.read1.D`, never set): dropped. -/
def stepClientRead (s : RState) (rid cid : w32) (k : w64) (d : Dep) :
    StepRes := do
  if !(k == 0 && slt d.key 0 && sge cid 0) then never
  if s.nReqs ≥ 24 then disabled
  if (cid, rid) ∈ s.used then disabled -- ghost guard: a fresh (client id, request id) here
  let s := { s with nReqs := s.nReqs + 1, used := (cid, rid) :: s.used }
  -- StartRead
  let n := s.maxN + 1
  let rop : ReadOp :=
    { requestId := rid, clientId := cid, n, maxValTag := none, readValTag := none,
      numRead1Replies := 1, -- `newRead` sets 0, then proxy mode: `r.numRead1Replies = 1`
      numRead2Replies := 0, readsWithMaxTag := 0, sentRead2Round := false,
      determinedReadVal := false, replicasWithMaxTag := [] }
  let mut s := { s with
    maxN := n,
    ongoingReqs := s.ongoingReqs.put n { requestId := rid, clientId := cid, isRead := true,
                                         shortReads := [] },
    rops := s.rops.put (shiftInts rid cid) rop }
  -- `for _, wop := range c.wops` (Go's order is random; each iteration appends `n` to one entry:
  -- the result does not depend on the order; the model visits the keys in increasing order)
  for (_, wop) in s.wops do
    if !wop.sentWrite2Round then -- `wop.Key == key` (both 0)
      let some op := s.ongoingReqs.get? wop.n
        | dead -- dead: a write's wops and OngoingReqs entries are deleted together
      s := { s with ongoingReqs := s.ongoingReqs.put wop.n
                                   { op with shortReads := op.shortReads ++ [n] } }
  -- replicas: every replica but this one (proxy), in increasing order; SendRead1
  let replicas : List w32 := [0, 1, 2].filter (fun i => i ≠ s.id)
  let m : Read1ProxiedM := { requestId := rid, clientId := cid, k := 0, d := dep0,
                             replicaId := s.id, vt := s.storeVT }
  let some outs := replicas.mapM (fun q => sendPeer s q (.read1 m))
    | dead -- dead: the replicas are peers
  return (s, outs)

/-- `handleRead1Reply` → `HandleRead1Reply(ShiftInts(RequestId, ClientId), &Vt, ReplicaId)`. -/
def stepRead1Reply (s : RState) (m : Read1ReplyM) : StepRes := do
  let id := shiftInts m.requestId m.clientId
  let some read := s.rops.get? id | return (s, [])
  let mut s := s
  let mut read := { read with numRead1Replies := read.numRead1Replies + 1 }
  let newMax : Bool := match read.maxValTag with
    | none => true
    | some mx => m.vt.t.gt mx.t
  if newMax then
    read := { read with maxValTag := some m.vt, replicasWithMaxTag := [] }
    -- proxy
    s := s.overwrite m.vt.v m.vt.t
    read := { read with readsWithMaxTag := 1, replicasWithMaxTag := [s.id] }
  let some mx := read.maxValTag | dead -- dead: set just above when nil
  if m.vt.t = mx.t then
    read := { read with readsWithMaxTag := read.readsWithMaxTag + 1,
                        replicasWithMaxTag := read.replicasWithMaxTag ++ [m.replicaId] }
  if sge read.numRead1Replies (NHALF + 1) then
    if !read.determinedReadVal then
      read := { read with readValTag := read.maxValTag, determinedReadVal := true }
    if sge read.readsWithMaxTag (NHALF + 1) then -- `c.regular` is false
      s := { s with ongoingReqs := s.ongoingReqs.del read.n, rops := s.rops.del id }
      let some rv := read.readValTag | dead -- dead: set just above
      return (s, [.ext (.readReply read.clientId read.requestId rv.v 1)])
    else if !read.sentRead2Round then
      let replicas : List w32 := [0, 1, 2].filter (fun i => !(read.replicasWithMaxTag.contains i))
      read := { read with numRead2Replies := 3 - BitVec.ofNat 64 replicas.length }
      let some rv := read.readValTag | dead -- dead: set just above
      let m2 : Read2ProxiedM := { requestId := read.requestId, clientId := read.clientId, k := 0,
                                  vt := rv, replicaId := s.id }
      let some outs := replicas.mapM (fun q => sendTo q (.read2 m2))
        | dead -- dead: replica ids
      read := { read with sentRead2Round := true }
      return ({ s with rops := s.rops.put id read }, outs)
  return ({ s with rops := s.rops.put id read }, [])

/-- `handleRead2Reply` → `HandleRead2Reply(ShiftInts(RequestId, ClientId), T, ReplicaId)`. -/
def stepRead2Reply (s : RState) (m : Read2ReplyM) : StepRes := do
  let id := shiftInts m.requestId m.clientId
  let some read := s.rops.get? id | return (s, [])
  let read := { read with numRead2Replies := read.numRead2Replies + 1 }
  if sge read.numRead2Replies (NHALF + 1) then
    let s := { s with ongoingReqs := s.ongoingReqs.del read.n, rops := s.rops.del id }
    let some rv := read.readValTag
      | dead -- dead: a Read2 was sent, after the read value was determined
    return (s, [.ext (.readReply read.clientId read.requestId rv.v 1)])
  return ({ s with rops := s.rops.put id read }, [])

/-- The client's Write (`writeChan` → `handleWrite` → `StartWrite(RequestId, ClientId, K, V, &D)`).
`forceWrite = 1` (line 485), so the concurrent-writes branch is not taken; `MaxTags` dropped. The
guard as `stepClientRead`'s (`D.Key < 0`); `D` is stored in the write op (`Op.Dep`) and forwarded
by `SendWrite1` as `Write1Proxied.D` (whose receivers do nothing with it: `D.Key < 0`). -/
def stepClientWrite (s : RState) (rid cid : w32) (k v : w64) (d : Dep) :
    StepRes := do
  if !(k == 0 && slt d.key 0 && sge cid 0) then never
  if s.nReqs ≥ 24 then disabled
  if (cid, rid) ∈ s.used then disabled -- ghost guard: a fresh (client id, request id) here
  let s := { s with nReqs := s.nReqs + 1, used := (cid, rid) :: s.used }
  let n := s.maxN + 1
  let w : WriteOp :=
    { requestId := rid, clientId := cid, n, writeValue := v, dep := d, maxValTag := ⟨-1, tag0⟩,
      numWrite1Applies := 0, numWrite1Replies := 0, numWrite2Applies := 0, numWrite2Replies := 0,
      sentWrite2Round := false, writeTag := none }
  let s := { s with
    maxN := n,
    wops := s.wops.put (shiftInts rid cid) w,
    ongoingReqs := s.ongoingReqs.put n { requestId := rid, clientId := cid, isRead := false,
                                         shortReads := [] } }
  -- SendWrite1(w, c.allReplicas)
  let m : Write1ProxiedM := { requestId := rid, clientId := cid, forceWrite := 1, k := 0,
                              d := w.dep, replicaId := s.id }
  let some outs := ([0, 1, 2] : List w32).mapM (fun q => sendTo q (.write1 m)) | dead -- dead: ids
  return (s, outs)

/-- `handleWrite1Reply` → `HandleWrite1Reply(ShiftInts(RequestId, ClientId), ClientId,
ReplicaId, &Vt)`. -/
def stepWrite1Reply (s : RState) (m : Write1ReplyM) : StepRes := do
  let id := shiftInts m.requestId m.clientId
  let some w := s.wops.get? id | return (s, [])
  let mut w := { w with numWrite1Replies := w.numWrite1Replies + 1 }
  if m.vt.t.gt w.maxValTag.t then
    w := { w with maxValTag := m.vt, numWrite1Applies := if sge m.vt.v 0 then 1 else 0 }
  else if m.vt.t.eqT w.maxValTag.t then
    if m.vt.v == w.maxValTag.v && sge w.maxValTag.v 0 then
      w := { w with numWrite1Applies := w.numWrite1Applies + 1 }
  if sge w.numWrite1Replies (NHALF + 1) then
    if sge w.numWrite1Applies (NHALF + 1) then
      let some (s, outs) := shortCircuit s w.n w.maxValTag true | dead -- dead: see shortCircuit
      let s := { s with wops := s.wops.del id, ongoingReqs := s.ongoingReqs.del w.n }
      return (s, outs ++ [.ext (.writeReply w.clientId w.requestId 1)])
    else if !w.sentWrite2Round then -- `!write.startedShortcircuitTimeout` is always true
      let wt : Tag := ⟨w.maxValTag.t.ts + 1, m.clientId, 0⟩
      w := { w with writeTag := some wt }
      -- SendWrite2(write, c.allReplicas)
      let m2 : Write2ProxiedM := { requestId := w.requestId, clientId := w.clientId, k := 0,
                                   vt := ⟨w.writeValue, wt⟩, replicaId := s.id }
      let some outs := ([0, 1, 2] : List w32).mapM (fun q => sendTo q (.write2 m2))
        | dead -- dead: replica ids
      w := { w with sentWrite2Round := true }
      return ({ s with wops := s.wops.put id w }, outs)
  return ({ s with wops := s.wops.put id w }, [])

/-- `handleWrite2Reply` → `HandleWrite2Reply(ShiftInts(RequestId, ClientId), ReplicaId, &T,
ClientId, Applied)` (`epaxosMode` false; `maxAppliedTag`, `MaxTags` dropped). -/
def stepWrite2Reply (s : RState) (m : Write2ReplyM) : StepRes := do
  let id := shiftInts m.requestId m.clientId
  let some w := s.wops.get? id | return (s, [])
  let w := { w with numWrite2Replies := w.numWrite2Replies + 1,
                    numWrite2Applies := if sgt m.applied 0 then w.numWrite2Applies + 1
                                        else w.numWrite2Applies }
  if sge w.numWrite2Replies (NHALF + 1) then
    let some wt := w.writeTag
      | dead -- dead: `*write.WriteTag` (line 734): set when the Write2s were sent
    let some (s, outs) := (if sge w.numWrite2Applies (NHALF + 1)
        then shortCircuit s w.n ⟨w.writeValue, wt⟩ false else some (s, []))
      | dead -- dead: see shortCircuit
    let s := { s with wops := s.wops.del id, ongoingReqs := s.ongoingReqs.del w.n }
    return (s, outs ++ [.ext (.writeReply w.clientId w.requestId 1)])
  return ({ s with wops := s.wops.put id w }, [])

/-- The forced-write ticker (`forceWriteChan` → `handleForceWrite` → `HandleForceWrite`): it
resets `ForcedKeys` for the keys in `ForcedKeysChanged`, which is always empty (only
commented-out code appends to it); `ForcedKeys` is dropped (`StartWrite` overrides its value). -/
def stepForceWrite (s : RState) : StepRes := pure (s, [])

end Perennial.gryff.model
