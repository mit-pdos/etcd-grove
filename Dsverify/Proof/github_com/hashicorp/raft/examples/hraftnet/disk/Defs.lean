/-
(hraft_robust R3) The disk's images and their encodings (`disk.go`'s `encode`/`decode`, `snap.go`'s), and the
memory representations of `*Disk` and `*Snaps` (what their mutexes guard). `DISKCRASH.md` (R3's scratch) and
`notes/dsv-hraft.md` ("hraft_robust") are the design.

* `DiskImg`: what `dir/raft` holds (the log's entries by increasing index, the stable store's two association
  lists, the written commit index), `encImg` its bytes; `absL`/`absS` the two contracts' abstract states.
* `SnapImg`: what `dir/snap` holds (the next ID and, if any, the latest snapshot), `encSnap` its bytes.
* `diskMem d I stg`: `*Disk` `d`'s fields at the image `I` and staged index `stg`; `snapsMem s S`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Codec

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open github_com.hashicorp.raft proto

/-! ## `dir/raft` -/

/-- A stored entry: index, term, type, data, extensions (`AppendedAt` is not kept). -/
structure DEnt where
  idx : w64
  term : w64
  ty : w8
  data : List w8
  ext : List w8

/-- **What `dir/raft` holds.** -/
structure DiskImg where
  ents : List DEnt
  kv : List (List w8 × List w8)
  ikv : List (List w8 × w64)
  commit : w64

def encEnt (e : DEnt) : List w8 :=
  encU64 e.idx ++ encU64 e.term ++ encU64 (W64 (uint.Z e.ty)) ++ encBytes e.data ++ encBytes e.ext

def encKV (p : List w8 × List w8) : List w8 := encBytes p.1 ++ encBytes p.2

def encIKV (p : List w8 × w64) : List w8 := encBytes p.1 ++ encU64 p.2

/-- **`Disk.encode`'s bytes.** -/
def encImg (I : DiskImg) : List w8 :=
  encU64 (W64 I.ents.length) ++ I.ents.flatMap encEnt ++
  encU64 (W64 I.kv.length) ++ I.kv.flatMap encKV ++
  encU64 (W64 I.ikv.length) ++ I.ikv.flatMap encIKV ++ encU64 I.commit

/-- Strictly increasing indexes, all at least 1. -/
def IdxOk : List DEnt → Prop
  | [] => True
  | [e] => 1 ≤ uint.nat e.idx
  | e :: f :: es => 1 ≤ uint.nat e.idx ∧ uint.nat e.idx < uint.nat f.idx ∧ IdxOk (f :: es)

/-- **A well-formed image**: increasing indexes from 1 (the log), distinct keys (the stable store), every
list and byte string shorter than `2 ^ 63` (a Go slice's, so that the codec reads its length back). -/
structure DiskImg.Ok (I : DiskImg) : Prop where
  idx : IdxOk I.ents
  kvKeys : (I.kv.map Prod.fst).Nodup
  ikvKeys : (I.ikv.map Prod.fst).Nodup
  lens : I.ents.length < 2 ^ 63 ∧ I.kv.length < 2 ^ 63 ∧ I.ikv.length < 2 ^ 63
  entLens : ∀ e ∈ I.ents, e.data.length < 2 ^ 63 ∧ e.ext.length < 2 ^ 63
  kvLens : ∀ p ∈ I.kv, p.1.length < 2 ^ 63 ∧ p.2.length < 2 ^ 63
  ikvLens : ∀ p ∈ I.ikv, p.1.length < 2 ^ 63

/-- The protocol entry an entry stores. -/
def entOf (e : DEnt) : Entry := ⟨uint.nat e.term, uint.nat e.ty, e.data⟩

/-- The log's partial map. -/
def DiskImg.logM (I : DiskImg) : GMap Nat Entry :=
  GMap.ofList (I.ents.map fun e => (uint.nat e.idx, entOf e))

/-- The largest index held (`lastIndex`), `0` for an empty log. -/
def DiskImg.hi (I : DiskImg) : w64 :=
  match I.ents.getLast? with
  | none => W64 0
  | some e => e.idx

/-- **The log store's abstract state** at the image `I` and staged index `stg`. -/
def DiskImg.absL (I : DiskImg) (stg : w64) : LogAbs := ⟨I.logM, I.hi, stg, I.commit⟩

/-- **The stable store's abstract state** at the image `I`. -/
def DiskImg.absS (I : DiskImg) : StableAbs := ⟨GMap.ofList I.ikv, GMap.ofList I.kv⟩

/-! ## `dir/snap` -/

/-- A configuration's server: suffrage, ID, address. -/
structure SServer where
  suffrage : w64
  id : GoString
  addr : GoString

/-- The latest snapshot's metadata as `dir/snap` keeps it (no `Peers`; `Size` is the data's length). -/
structure SMeta where
  version : w64
  id : GoString
  index : w64
  term : w64
  servers : List SServer
  cfgIndex : w64

/-- **What `dir/snap` holds.** -/
structure SnapImg where
  nextID : w64
  latest : Option (SMeta × List w8)

def encServer (s : SServer) : List w8 := encU64 s.suffrage ++ encBytes s.id ++ encBytes s.addr

/-- `encodeConfiguration`'s bytes. -/
def encCfg (ss : List SServer) : List w8 := encU64 (W64 ss.length) ++ ss.flatMap encServer

/-- **`Snaps.encode`'s bytes.** -/
def encSnap (S : SnapImg) : List w8 :=
  encU64 S.nextID ++
  match S.latest with
  | none => encU64 (W64 0)
  | some (m, b) =>
    encU64 (W64 1) ++ encU64 m.version ++ encBytes m.id ++ encU64 m.index ++ encU64 m.term ++
      encCfg m.servers ++ encU64 m.cfgIndex ++ encBytes b

/-- A well-formed snapshot image (lengths of Go slices). -/
def SnapImg.Ok (S : SnapImg) : Prop :=
  match S.latest with
  | none => True
  | some (m, b) => m.id.length < 2 ^ 63 ∧ m.servers.length < 2 ^ 63 ∧ b.length < 2 ^ 63 ∧
      ∀ s ∈ m.servers, s.id.length < 2 ^ 63 ∧ s.addr.length < 2 ^ 63

section rep
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- A stored `Log` value holds the entry `e` (its byte slices read-only). -/
def entRep (lv : Log) (e : DEnt) : IProp GF :=
  iprop(⌜lv.Index' = e.idx ∧ lv.Term' = e.term ∧ lv.Type' = e.ty⌝ ∗
    lv.Data' ↦*□ e.data ∗ lv.Extensions' ↦*□ e.ext)

instance entRep_persistent lv e : Persistent (entRep (GF := GF) lv e) := by
  unfold entRep; infer_instance

/-- **`*Disk` `d`'s fields** (but `mu` and `file`, read-only) at the image `I` and staged index `stg`: the
slices owned, their elements' byte slices read-only. -/
def diskMem (d : Loc) (I : DiskImg) (stg : w64) : IProp GF :=
  iprop(∃ (es ks vs iks ivs : GoSlice) (lvs : List Log) (kss vss ikss : List GoSlice),
    d.[Disk, go!"ents"] ↦ es ∗ es ↦* lvs ∗ ownSliceCap Log es (DFrac.own 1) ∗
    ([∗list] lv; e ∈ lvs; I.ents, entRep lv e) ∗
    d.[Disk, go!"keys"] ↦ ks ∗ ks ↦* kss ∗ ownSliceCap GoSlice ks (DFrac.own 1) ∗
    ([∗list] k; p ∈ kss; I.kv, k ↦*□ p.1) ∗
    d.[Disk, go!"vals"] ↦ vs ∗ vs ↦* vss ∗ ownSliceCap GoSlice vs (DFrac.own 1) ∗
    ([∗list] v; p ∈ vss; I.kv, v ↦*□ p.2) ∗
    d.[Disk, go!"ikeys"] ↦ iks ∗ iks ↦* ikss ∗ ownSliceCap GoSlice iks (DFrac.own 1) ∗
    ([∗list] k; p ∈ ikss; I.ikv, k ↦*□ p.1) ∗
    d.[Disk, go!"ivals"] ↦ ivs ∗ ivs ↦* (I.ikv.map Prod.snd) ∗ ownSliceCap w64 ivs (DFrac.own 1) ∗
    d.[Disk, go!"staged"] ↦ stg ∗ d.[Disk, go!"commit"] ↦ I.commit)

end rep


/-! ## (codec round trip) The decoders' pre-states and `*Snaps`'s memory -/

section rep2
open Iris Iris.BI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **A fresh `*Disk`'s decoded fields** (`Open`'s `&Disk{mu: …, file: …}`): every slice nil, the staged and
written commit indexes zero. -/
def diskMem0 (d : Loc) : IProp GF :=
  iprop(d.[Disk, go!"ents"] ↦ slice.nil ∗ d.[Disk, go!"keys"] ↦ slice.nil ∗ d.[Disk, go!"vals"] ↦ slice.nil ∗
    d.[Disk, go!"ikeys"] ↦ slice.nil ∗ d.[Disk, go!"ivals"] ↦ slice.nil ∗
    d.[Disk, go!"staged"] ↦ W64 0 ∗ d.[Disk, go!"commit"] ↦ W64 0)

/-- The server a `Server` value holds. -/
def srvOf (sv : Server) : SServer := ⟨sv.Suffrage', sv.ID', sv.Address'⟩

/-- **A configuration value holds the servers `ss`**: its `Servers'` slice (read-only) holds `Server` values
whose servers are `ss`. -/
def cfgRep (c : Configuration) (ss : List SServer) : IProp GF :=
  iprop(∃ svs : List Server, c.Servers' ↦*□ svs ∗ ⌜svs.map srvOf = ss⌝)

instance cfgRep_persistent c ss : Persistent (cfgRep (GF := GF) c ss) := by
  unfold cfgRep; infer_instance

/-- **A `SnapshotMeta` value holds `m`**, with `Size` the data's length `n` and `Peers` nil (raft no longer
sets it). -/
def metaRep (mv : SnapshotMeta) (m : SMeta) (n : Nat) : IProp GF :=
  iprop(⌜mv.Version' = m.version ∧ mv.ID' = m.id ∧ mv.Index' = m.index ∧ mv.Term' = m.term ∧
      mv.Peers' = slice.nil ∧ mv.ConfigurationIndex' = m.cfgIndex ∧ mv.Size' = W64 (n : Int)⌝ ∗
    cfgRep mv.Configuration' m.servers)

instance metaRep_persistent mv m n : Persistent (metaRep (GF := GF) mv m n) := by
  unfold metaRep; infer_instance

/-- **`*Snaps` `s`'s fields** (but `mu` and `file`) at the image `S`: without a snapshot `has` is false (the
metadata and data fields hold anything); with one, the metadata holds it and the data (read-only) its bytes. -/
def snapsMem (s : Loc) (S : SnapImg) : IProp GF :=
  iprop(∃ (has : Bool) (mv : SnapshotMeta) (dt : GoSlice),
    s.[Snaps, go!"has"] ↦ has ∗ s.[Snaps, go!"meta"] ↦ mv ∗ s.[Snaps, go!"data"] ↦ dt ∗
    s.[Snaps, go!"nextID"] ↦ S.nextID ∗
    match S.latest with
    | none => ⌜has = false⌝
    | some (m, b) => ⌜has = true⌝ ∗ metaRep mv m b.length ∗ dt ↦*□ b)

/-- **A fresh `*Snaps`'s decoded fields** (`OpenSnaps`'s `&Snaps{mu: …, file: …}`): no snapshot, the rest
anything. -/
def snapsMem0 (s : Loc) : IProp GF :=
  iprop(∃ (mv : SnapshotMeta) (dt : GoSlice) (nid : w64),
    s.[Snaps, go!"has"] ↦ false ∗ s.[Snaps, go!"meta"] ↦ mv ∗ s.[Snaps, go!"data"] ↦ dt ∗
    s.[Snaps, go!"nextID"] ↦ nid)

end rep2

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
