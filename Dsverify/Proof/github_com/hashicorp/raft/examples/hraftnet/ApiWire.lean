/-
The wire values of the hraft kit's API service (package `service`'s argument and reply structs) as
pure records, their encodings by the kit's generated codec (`examples/hraftnet/rpc_gen.go`, by
`models/net/rpc/rpcgen.py`: `rpcEnc_t37` ... `rpcEnc_t49`), in `rpctransport/WireEnc.lean`'s format,
and the ownership of a struct by its record (notes/dsv-hraft.md, S5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.CodecLaws
public import Dsverify.GeneratedProof.github_com.hashicorp.raft.examples.hraftnet.service

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.hashicorp.raft.examples.hraftnet

open rpctransport

/-! ## The wire values and their encodings -/

/-- An `ApplyArgs`. -/
structure ApplyArgsV where
  data : List w8

def encApplyArgs (v : ApplyArgsV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/service.ApplyArgs" (strct [fBytes v.data])

/-- An `ApplyReply`. -/
structure ApplyReplyV where
  status : w64
  found : Bool
  v : List w8

def encApplyReply (v : ApplyReplyV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/service.ApplyReply"
    (strct [fU64 v.status, fBool v.found, fStr v.v])

/-- A `ReadArgs`. -/
structure ReadArgsV where
  way : w64

def encReadArgs (v : ReadArgsV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/service.ReadArgs" (strct [fU64 v.way])

/-- A `ReadReply`. -/
structure ReadReplyV where
  ok : Bool
  found : Bool
  v : List w8

def encReadReply (v : ReadReplyV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/service.ReadReply"
    (strct [fBool v.ok, fBool v.found, fStr v.v])

/-- An `AdminArgs`. -/
structure AdminArgsV where
  id : List w8
  addr : List w8

def encAdminArgs (v : AdminArgsV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/service.AdminArgs" (strct [fStr v.id, fStr v.addr])

/-- An `AdminReply`. -/
structure AdminReplyV where
  ok : Bool

def encAdminReply (v : AdminReplyV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/service.AdminReply" (strct [fBool v.ok])

/-- A `StatusReply`. -/
structure StatusReplyV where
  leader : Bool
  leaderID : List w8
  configured : Bool
  servers : w64
  voters : w64

def encStatusReply (v : StatusReplyV) : List w8 :=
  tagged go!"github.com/hashicorp/raft/examples/hraftnet/service.StatusReply"
    (strct [fBool v.leader, fStr v.leaderID, fBool v.configured, fU64 v.servers, fU64 v.voters])

section own
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open service

/-! ## Ownership of the structs, by their values -/

def applyArgsOwn (w : ApplyArgs) (dq : DFrac) (v : ApplyArgsV) : IProp GF :=
  iprop(w.Data' ↦*{dq} v.data)

def applyReplyOwn (w : ApplyReply) (_dq : DFrac) (v : ApplyReplyV) : IProp GF :=
  iprop(⌜w.Status' = v.status ∧ w.Found' = v.found ∧ w.V' = v.v⌝)

def readArgsOwn (w : ReadArgs) (_dq : DFrac) (v : ReadArgsV) : IProp GF :=
  iprop(⌜w.Way' = v.way⌝)

def readReplyOwn (w : ReadReply) (_dq : DFrac) (v : ReadReplyV) : IProp GF :=
  iprop(⌜w.Ok' = v.ok ∧ w.Found' = v.found ∧ w.V' = v.v⌝)

def adminArgsOwn (w : AdminArgs) (_dq : DFrac) (v : AdminArgsV) : IProp GF :=
  iprop(⌜w.ID' = v.id ∧ w.Addr' = v.addr⌝)

def adminReplyOwn (w : AdminReply) (_dq : DFrac) (v : AdminReplyV) : IProp GF :=
  iprop(⌜w.Ok' = v.ok⌝)

def statusReplyOwn (w : StatusReply) (_dq : DFrac) (v : StatusReplyV) : IProp GF :=
  iprop(⌜w.Leader' = v.leader ∧ w.LeaderID' = v.leaderID ∧ w.Configured' = v.configured ∧
    w.Servers' = v.servers ∧ w.Voters' = v.voters⌝)

end own

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
