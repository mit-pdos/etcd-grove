/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Own.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Copies of `Spec/swiftnet/Codec.lean`'s definitions (the codec's ownership of Go values and the
pure merge), under `C`-suffixed names, for the codec's proofs: `Codec.lean` imports this module
for its proofs, so the proofs cannot import `Codec.lean`; `Codec.lean` proves each copy equal to
its original (`rfl`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

/-! ## Values of the listed types -/

namespace sp

/-- Two codec values that differ only in the iteration order of an `MSync`'s maps (the encoder
iterates Go maps in an arbitrary order). -/
def KitVal.equivC : KitVal → KitVal → Prop
  | .msync m, .msync m' => m.rep = m'.rep ∧ m.bal = m'.bal ∧
      Option.Rel List.Perm m.phases m'.phases ∧ Option.Rel List.Perm m.cmds m'.cmds ∧
      Option.Rel List.Perm m.deps m'.deps
  | x, y => x = y

/-- The value is well formed: an `MSync`'s map listings have distinct keys (what Go maps
encode). -/
def KitVal.wfC : KitVal → Prop
  | .msync m => (m.phases.map (fun l => (l.map Prod.fst).Nodup)).getD True ∧
      (m.cmds.map (fun l => (l.map Prod.fst).Nodup)).getD True ∧
      (m.deps.map (fun l => (l.map Prod.fst).Nodup)).getD True
  | _ => True

/-- gob's merge of a decoded value `y` into a target holding `x` of the same type
(`rpcMerge_*`): a zero field of `y` (gob does not send it), an empty slice, and a nil map leave
`x`'s; every other field is `y`'s. For two values of different types, `y`. -/
def KitVal.mergeC : KitVal → KitVal → KitVal
  | .registerArgs a p, .registerArgs a' p' =>
      .registerArgs (if a' = [] then a else a') (if p' = 0 then p else p')
  | .registerReply i ns r l, .registerReply i' ns' r' l' =>
      .registerReply (if i' = 0 then i else i') (if ns' = [] then ns else ns') (r || r') (l || l')
  | .getLeaderReply i, .getLeaderReply i' => .getLeaderReply (if i' = 0 then i else i')
  | .getReplicaListReply rs al r, .getReplicaListReply rs' al' r' =>
      .getReplicaListReply (if rs' = [] then rs else rs') (if al' = [] then al else al') (r || r')
  | .pingArgs a, .pingArgs a' => .pingArgs (if a' = 0 then a else a')
  | .beTheLeaderReply l n, .beTheLeaderReply l' n' =>
      .beTheLeaderReply (if l' = 0 then l else l') (if n' = 0 then n else n')
  | .msync m, .msync m' =>
      .msync ⟨if m'.rep = 0 then m.rep else m'.rep, if m'.bal = 0 then m.bal else m'.bal,
        m'.phases.or m.phases, m'.cmds.or m.cmds, m'.deps.or m.deps⟩
  | _, y => y

end sp

/-- The id of a `swift.CommandId` struct. -/
def goCmdIdC [GooseExts] (c : swift.CommandId) : sp.CmdId := ⟨c.ClientId', c.SeqNum'⟩

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [examples.swiftnet.Assumptions]

/-- The Go command `c` holds `x` (its value's slice with fraction `dq`). -/
def cmdOwnC (c : state.Command) (dq : DFrac) (x : sp.Cmd) : IProp GF :=
  iprop(⌜c.Op' = x.op ∧ c.K' = x.key⌝ ∗ c.V' ↦*{dq} x.val)

/-- The Go map at `mp` (`nil`: `none`) holds the entries `l`, in the order of the Go entries
`ps` (distinct keys) its value lists, with the fraction `dq`, the values related by `R`. (Stated
on the map's heap value as `ownMap`'s definition is, `Perennial/Golang/Theory/Map.lean`, without
`ownMap`'s instance `go.IntoValInj swift.CommandId`, which no module provides.) -/
def mapOwnC {V A : Type} [ZeroVal V] (mp : GoMap) (dq : DFrac)
    (R : V → A → IProp GF) : Option (List (sp.CmdId × A)) → IProp GF
  | none => iprop(⌜mp = map.nil⌝)
  | some l => iprop(∃ (mv : val) (ps : List (swift.CommandId × V)),
      heapPointsto mp dq mv ∗
      ⌜mv = map.mapV #(zero_val V) (ps.map map.toE) ∧ (ps.map Prod.fst).Nodup ∧
        ps.map (fun p => goCmdIdC p.1) = l.map Prod.fst⌝ ∗
      [∗list] i ↦ e ∈ l, ∃ p : swift.CommandId × V, ⌜ps[i]? = some p⌝ ∗ R p.2 e.2)

/-- The struct value `s` of a listed type holds `x`, its slices' and maps' contents with the
fraction `dq` (pure fields equal). -/
def structOwnC (ty : go.GoType) (p : Loc) (dq : DFrac) : sp.KitVal → IProp GF
  | .registerArgs a pt => iprop(⌜ty = replica.defs.RegisterArgs.ty⌝ ∗
      p ↦{dq} (⟨a, pt⟩ : replica.defs.RegisterArgs))
  | .registerReply i ns r l => iprop(⌜ty = replica.defs.RegisterReply.ty⌝ ∗
      ∃ sl : GoSlice, p ↦{dq} (⟨i, sl, r, l⟩ : replica.defs.RegisterReply) ∗ sl ↦*{dq} ns)
  | .getLeaderArgs => iprop(⌜ty = replica.defs.GetLeaderArgs.ty⌝ ∗
      ∃ s : replica.defs.GetLeaderArgs, p ↦{dq} s)
  | .getLeaderReply i => iprop(⌜ty = replica.defs.GetLeaderReply.ty⌝ ∗
      p ↦{dq} (⟨i⟩ : replica.defs.GetLeaderReply))
  | .getReplicaListArgs => iprop(⌜ty = replica.defs.GetReplicaListArgs.ty⌝ ∗
      ∃ s : replica.defs.GetReplicaListArgs, p ↦{dq} s)
  | .getReplicaListReply rs al r => iprop(⌜ty = replica.defs.GetReplicaListReply.ty⌝ ∗
      ∃ s1 s2 : GoSlice, p ↦{dq} (⟨s1, s2, r⟩ : replica.defs.GetReplicaListReply) ∗
        s1 ↦*{dq} rs ∗ s2 ↦*{dq} al)
  | .pingArgs a => iprop(⌜ty = replica.defs.PingArgs.ty⌝ ∗
      p ↦{dq} (⟨a⟩ : replica.defs.PingArgs))
  | .pingReply => iprop(⌜ty = replica.defs.PingReply.ty⌝ ∗
      ∃ s : replica.defs.PingReply, p ↦{dq} s)
  | .beTheLeaderArgs => iprop(⌜ty = replica.defs.BeTheLeaderArgs.ty⌝ ∗
      ∃ s : replica.defs.BeTheLeaderArgs, p ↦{dq} s)
  | .beTheLeaderReply l n => iprop(⌜ty = replica.defs.BeTheLeaderReply.ty⌝ ∗
      p ↦{dq} (⟨l, n⟩ : replica.defs.BeTheLeaderReply))
  | .msync m => iprop(⌜ty = swift.MSync.ty⌝ ∗
      ∃ ph cm dp : GoMap, p ↦{dq} (⟨m.rep, m.bal, ph, cm, dp⟩ : swift.MSync) ∗
        mapOwnC (V := w64) ph dq (fun v a => iprop(⌜v = a⌝)) m.phases ∗
        mapOwnC (V := state.Command) cm dq (fun c x => cmdOwnC c dq x) m.cmds ∗
        mapOwnC (V := swift.Dep) dp dq
          (fun sl d => iprop(∃ ids : List swift.CommandId, sl ↦*{dq} ids ∗
            ⌜ids.map goCmdIdC = d⌝)) m.deps)

/-- The Go value `v` is a non-nil pointer to a value of one of the kit's listed types holding
`x`, with the fraction `dq` (see `structOwnC`). -/
def kitValOwnC (v : GoInterface) (dq : DFrac) (x : sp.KitVal) : IProp GF :=
  iprop(∃ (ty : go.GoType) (p : Loc), ⌜v = interface.mkOk (go.GoType.PointerType ty) #p ∧
    p ≠ null⌝ ∗ structOwnC ty p dq x)

end own


end Perennial.github_com.imdea_software.swiftpaxos
