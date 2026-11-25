/-
**The vocabulary of `createHeaderFields`' spec** (phase 7 S2 core, 2026-11-23, `notes/phase7-plan.md`
§0a): the head's fields as Lean functions of the call header, the connection's user agent, the
credentials' metadata and the context's outgoing metadata (`models/grpc/model_transport.go`,
grpc-go's `http2Client.createHeaderFields`). Definitions and pure laws; no axiom. Lean-first.

**The order of the fields.** grpc writes, in this order: the call header's fields (`callHdrFields`:
the pseudo-headers, `content-type`, `user-agent`, `te`, then `grpc-previous-rpc-attempts`,
`grpc-encoding`, `grpc-accept-encoding` when they apply), `grpc-timeout` if the context has a
deadline (`timeoutFieldsOk`: the deadline's remaining duration is not known, only positive), the
credentials' metadata (`credsFieldsOk`), then the context's outgoing metadata (`outFieldsOk`). The
credentials' and the context's metadata are maps, which Go ranges over in an arbitrary order: their
fields are stated for some enumeration `keys` of the map's keys (`enumKeys`), any one, as
`grpcFieldsMd` (`InvGrpcWire`) needs: it reads each key's values in order, and a key's values are
contiguous here.

**The credentials** (`hdrCredsOk pc Ok Q`): `pc` is not `nil` (grpc calls its method), and
`pc.GetRequestMetadata` returns, given a resource of the
family `Ok` (the connection's, `perRPCCredsOk`), either an error that grpc's `status` accepts (grpc
returns it, or a status error made of it: the attempt's error arm) or a map (`nil` for none,
`credsMapAt`) whose keys are lower case and no pseudo-header (`credKeysOk`: `ValidateKey` skips
keys starting with `:`, which `createHeaderFields` would append after the real `:path`, §0a's finding;
grpc lower-cases the keys, so a lower-case key is the one sent) and that meets `Q`.

**The context's outgoing metadata** (`outRawIs ctx o`): what grpc's transport reads of the context
(`metadataFromOutgoingContextRaw`: the `rawMD` at `mdOutgoingKey{}`), its map's values and its
`added` rows, read-only, with the rows' keys lower case (`AppendToOutgoingContext` lower-cases them).
`outRawIs_of_outMD` relates it to `metadata.outMD ctx md` (2026-11-23: `metadata.builtRawMDRaw`, until then a
trusted opaque with no law, is defined by the `rawMD`'s contents): the transport reads raw contents whose
merged view (`outViewOf`) is `md`.

`grpc.outRawFn.law`: grpc's package variable `metadataFromOutgoingContextRaw` holds `metadata`'s
`fromOutgoingContextRaw`; proved, `grpc.outRawFn_law_holds`, from grpc's package fact (`grpcInit`,
W1, 2026-11-26).
-/
module

public import Proof.google_golang_org.grpc.HeaderFields
public import Proof.google_golang_org.grpc.InvGrpc
public import Proof.context.LibKeys
public import Proof.context.LibKeysChain
public import Proof.strings.Lower

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace grpcHdr

/-! ## The call header's fields -/

/-- The fields grpc always writes first. -/
def baseFields (method host sub ua : GoString) : List (GoString × GoString) :=
  [(go!":method", go!"POST"), (go!":scheme", go!"http"), (go!":path", method),
    (go!":authority", host), (go!"content-type", contentTypeOf sub), (go!"user-agent", ua),
    (go!"te", go!"trailers")]

/-- `grpc-previous-rpc-attempts`, for a retry. -/
def prevFields (n : w64) : List (GoString × GoString) :=
  if 0 < sint.Z n then
    [(go!"grpc-previous-rpc-attempts", _root_.Perennial.internal.strconv.fmtInt n (W64 10))]
  else []

/-- The accepted compressors grpc advertises: the call's (`acc`), with the call's compressor `sc`
appended (no compressor is registered in the model: `IsCompressorNameRegistered` is `false`). -/
def regCompOf (acc sc : GoString) : GoString :=
  if sc = [] then acc else (if acc = [] then [] else acc ++ go!",") ++ sc

def encFields (sc : GoString) : List (GoString × GoString) :=
  if sc = [] then [] else [(go!"grpc-encoding", sc)]

def acceptFields (acc sc : GoString) : List (GoString × GoString) :=
  if regCompOf acc sc = [] then [] else [(go!"grpc-accept-encoding", regCompOf acc sc)]

/-- **The call header's fields**, for the accepted compressors `acc` (`*callHdr.AcceptedCompressors`,
`""` for none) and the connection's user agent `ua`. -/
def callHdrFields [GooseExts] (ch : google_golang_org.grpc.callHdr) (acc ua : GoString) :
    List (GoString × GoString) :=
  baseFields ch.Method' ch.Host' ch.ContentSubtype' ua ++ prevFields ch.PreviousAttempts' ++
    encFields ch.SendCompress' ++ acceptFields acc ch.SendCompress'

/-- `grpc-timeout`, if the context has a deadline: the remaining duration, positive (else the call
fails). -/
def timeoutFieldsOk (tfs : List (GoString × GoString)) : Prop :=
  tfs = [] ∨ ∃ d : w64, 0 < sint.Z d ∧ tfs = [(go!"grpc-timeout", encodeDurationOf d)]

/-! ## Maps' fields -/

/-- `keys` enumerates the keys of `m`, each once (an order Go's `range` may take). -/
def enumKeys {V : Type} (m : GoString → Option V) (keys : List GoString) : Prop :=
  keys.Nodup ∧ ∀ k, k ∈ keys ↔ (m k).isSome

/-- The credentials' metadata after their maps `cms` were merged in order (`authData[k] = v`: a later
map's value wins). -/
def credsLookup (cms : List (GMap GoString GoString)) (k : GoString) : Option GoString :=
  cms.foldl (fun acc m => (m !! k).or acc) none

/-- A map's fields in the order `keys`, each value encoded (`encodeMetadataHeader`). -/
def mapFields (keys : List GoString) (look : GoString → Option GoString) :
    List (GoString × GoString) :=
  keys.filterMap fun k => (look k).map fun v => (k, encMdHdr k v)

/-- **The credentials' fields**: the merged maps', in some order. -/
def credsFieldsOk (cms : List (GMap GoString GoString)) (afs : List (GoString × GoString)) : Prop :=
  ∃ keys, enumKeys (credsLookup cms) keys ∧ afs = mapFields keys (credsLookup cms)

/-- A credentials map grpc sends unchanged: lower-case keys (`strings.ToLower` keeps them), none a
pseudo-header. -/
def credKeysOk (cm : GMap GoString GoString) : Prop :=
  ∀ k v, cm !! k = some v → strings.lowerWord k ∧ k.head? ≠ some (W8 58)

/-- A key of the outgoing metadata's map: its values' fields, none for a reserved key. -/
def mdKeyFields (k : GoString) (vs : List GoString) : List (GoString × GoString) :=
  if reservedHdr k then [] else vs.map fun v => (k, encMdHdr k v)

/-- An `added` row (`k1, v1, k2, v2, ...`): its pairs' fields, none for a reserved key. -/
def rowFields : List GoString → List (GoString × GoString)
  | k :: v :: rest => (if reservedHdr k then [] else [(k, encMdHdr k v)]) ++ rowFields rest
  | _ => []

/-- A row's keys (its even entries) are lower case. -/
def rowKeysLower (row : List GoString) : Prop :=
  ∀ (i : Nat) (h : i < row.length), i % 2 = 0 → strings.lowerWord row[i]

/-- **The outgoing metadata's fields**: none without a `rawMD`; else the map's, in some order of its
keys, then the rows'. -/
def outFieldsOk : Option (GMap GoString (List GoString) × List (List GoString)) →
    List (GoString × GoString) → Prop
  | none, ofs => ofs = []
  | some (M, rows), ofs => ∃ keys, enumKeys (M !! ·) keys ∧
      ofs = keys.flatMap (fun k => mdKeyFields k ((M !! k).getD [])) ++ rows.flatMap rowFields

/-! ## Laws -/

theorem lowersTo_self : ∀ w : GoString, strings.lowersTo w w = true
  | [] => rfl
  | b :: w => by
    simp only [strings.lowersTo, strings.lowerAlts, List.any_cons, List.isPrefixOf,
      beq_self_eq_true, Bool.true_and, List.length_singleton, List.drop_succ_cons, List.drop_zero,
      lowersTo_self w, Bool.true_or]

theorem credsLookup_snoc (cms : List (GMap GoString GoString)) (m : GMap GoString GoString)
    (k : GoString) : credsLookup (cms ++ [m]) k = (m !! k).or (credsLookup cms k) := by
  simp [credsLookup, List.foldl_append]

theorem mapFields_snoc (keys : List GoString) (k : GoString) (look : GoString → Option GoString)
    (v : GoString) (h : look k = some v) :
    mapFields (keys ++ [k]) look = mapFields keys look ++ [(k, encMdHdr k v)] := by
  simp [mapFields, List.filterMap_append, h]

theorem rowFields_append : ∀ (l rest : List GoString), l.length % 2 = 0 →
    rowFields (l ++ rest) = rowFields l ++ rowFields rest
  | [], rest, _ => by simp [rowFields]
  | [_], _, h => by simp at h
  | a :: b :: l, rest, h => by
    simp only [List.cons_append, rowFields]
    rw [rowFields_append l rest (by simp at h; omega)]
    simp

/-- Go's `i%2 == 0` on a non-negative `int` (signed remainder). -/
theorem srem2_eq_zero (n : w64) (h : 0 ≤ sint.Z n) :
    BitVec.srem n (W64 2) = W64 0 ↔ sint.nat n % 2 = 0 := by
  have hmsb : n.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    have := BitVec.toInt_eq_toNat_of_lt (x := n)
    simp only [sint.Z] at h
    rw [BitVec.toInt_eq_toNat_cond] at h
    split at h <;> omega
  rw [BitVec.srem_eq]
  simp only [hmsb, show (W64 2).msb = false by decide]
  simp only [sint.nat]
  rw [BitVec.toInt_eq_toNat_of_msb hmsb]
  constructor
  · intro h2
    have := congrArg BitVec.toNat h2
    simp at this
    omega
  · intro h2
    apply BitVec.eq_of_toNat_eq
    simp
    omega

end grpcHdr

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A credentials map: `nil` and empty, or read-only. -/
def credsMapAt (mp : Loc) (cm : GMap GoString GoString) : IProp GF :=
  iprop(⌜mp = null ∧ cm = ∅⌝ ∨ ownMap mp DFrac.discard cm)

instance credsMapAt_persistent (mp : Loc) (cm : GMap GoString GoString) :
    Persistent (credsMapAt (GF := GF) mp cm) := by
  unfold credsMapAt; infer_instance

/-- **The per-RPC credentials `pc` as `createHeaderFields` calls them** (persistent; see the file
header). -/
def hdrCredsOk (pc : GoInterface) (Ok : IProp GF → Prop) (Q : GMap GoString GoString → IProp GF) :
    IProp GF :=
  iprop(∃ pci : GoInterfaceOk, ⌜pc = GoInterface.ok pci⌝ ∗
    □ ∀ (ctx : GoInterface) (sl : GoSlice) (R : IProp GF),
    {{ ⌜Ok R⌝ ∗ R }}
      (App (App (Val #(methods pci.ty go!"GetRequestMetadata" pci.v)) (Val #ctx)) (Val #sl))
    {{ (mp : Loc) (err : GoInterface), RET (PairV #mp #err); R ∗
        ((⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.statusErrOk err ∗
            ∃ (m : GoString) (c : w32), go_etcd_io.etcd.cache.v3.descIs err m ∗
              go_etcd_io.etcd.cache.v3.statusCodeIs err c) ∨
          (⌜err = GoInterface.nil⌝ ∗ ∃ cm, credsMapAt mp cm ∗ ⌜grpcHdr.credKeysOk cm⌝ ∗ □ Q cm)) }})

instance hdrCredsOk_persistent (pc : GoInterface) (Ok : IProp GF → Prop)
    (Q : GMap GoString GoString → IProp GF) : Persistent (hdrCredsOk pc Ok Q) := by
  unfold hdrCredsOk; infer_instance

/-- **The context's outgoing metadata as grpc's transport reads it** (persistent; see the file
header): `Value(mdOutgoingKey{})` returns one `v`; with `o = none`, no `rawMD`; with
`o = some (M, rows)`, a `rawMD` whose map (`nil` and empty, or read-only) has the values `M` and whose
`added` rows are `rows`, read-only, their keys lower case. -/
def outRawIs (ctx : GoInterfaceOk)
    (o : Option (GMap GoString (List GoString) × List (List GoString))) : IProp GF :=
  iprop(∃ v : GoInterface, context.valueAt ctx metadata.mdOutgoingKeyAny (· = v) ∗
    match o with
    | none => ⌜∀ vi : GoInterfaceOk, v = GoInterface.ok vi →
        vi.ty ≠ google_golang_org.grpc.metadata.rawMD.ty⌝
    | some (M, rows) => □ ∃ (r : google_golang_org.grpc.metadata.rawMD)
        (ms : GMap GoString GoSlice) (rsl : List GoSlice),
      ⌜v = interface.mkOk google_golang_org.grpc.metadata.rawMD.ty #r⌝ ∗
      (⌜r.md' = null ∧ ms = ∅⌝ ∨ ownMap r.md' DFrac.discard ms) ∗
      ⌜∀ k, (M !! k).isSome = (ms !! k).isSome⌝ ∗
      ([∗map] k ↦ sl ∈ ms, sl ↦*□ ((M !! k).getD [])) ∗
      r.added' ↦*□ rsl ∗ ⌜rsl.length = rows.length ∧ ∀ row ∈ rows, grpcHdr.rowKeysLower row⌝ ∗
      ([∗list] i ↦ sl ∈ rsl, sl ↦*□ (rows.getD i [])))

instance outRawIs_persistent (ctx : GoInterfaceOk)
    (o : Option (GMap GoString (List GoString) × List (List GoString))) :
    Persistent (outRawIs (GF := GF) ctx o) := by
  unfold outRawIs; cases o with
  | none => infer_instance
  | some p => obtain ⟨M, rows⟩ := p; dsimp only; infer_instance

/-- The outgoing metadata of the raw contents `o` (`FromOutgoingContext`'s view). -/
def outViewOf (o : Option (GMap GoString (List GoString) × List (List GoString))) :
    Option (GoString → Option (List GoString)) :=
  o.map fun p => metadata.rawView p.1 p.2

/-- **A context's outgoing metadata, as the transport reads it** (since `builtRawMDRaw` is a definition,
2026-11-23): of a context whose outgoing metadata is `md` (`metadata.outMD`), the transport reads raw
contents `o` (`outRawIs`) whose view is `md`. -/
theorem outRawIs_of_outMD [_root_.Perennial.context.Assumptions] (ctx : GoInterfaceOk)
    (md : Option (GoString → Option (List GoString))) :
    isPkgInit (PROP := IProp GF) pkg_id.context ∗ metadata.outMD ctx md ⊢
      ∃ o, outRawIs ctx o ∗ ⌜md = outViewOf o⌝ := by
  iintro ⟨#Hpkg, #H⟩
  unfold metadata.outMD
  icases H with ⟨%v, #Hv, #Hh⟩
  ihave #Hva := context.valueAt_of_ctxValue ctx metadata.mdOutgoingKeyAny (· = v) $$ [Hpkg Hv]
  · iframe #
  unfold metadata.outgoingHeld
  icases Hh with (%hn | ⟨%f, %hf, #Hb⟩)
  · obtain ⟨hmd, hty⟩ := hn
    iexists none
    isplitl []
    · unfold outRawIs
      iexists v
      iframe Hva
      ipureintro; exact hty
    · ipureintro; simp [hmd, outViewOf]
  · unfold metadata.builtRawMDRaw
    icases Hb with ⟨%M, %rows, #Hr, %hv⟩
    iexists (some (M, rows))
    isplitl []
    · unfold outRawIs
      iexists v
      iframe Hva
      unfold metadata.rawMDAt
      icases Hr with ⟨%r, %ms, %rsl, %hvr, #Hm, %hk, #Hms, #Ha, %hl, #Hrs, %hok⟩
      imodintro
      iexists r, ms, rsl
      iframe #
      ipureintro
      refine ⟨hvr, hk, hl, ?_⟩
      intro row hrow i hi he
      exact (hok.2 row hrow).2 i hi he
    · ipureintro; simp [hf, hv, outViewOf]

/-- **grpc's `metadataFromOutgoingContextRaw` holds `metadata.fromOutgoingContextRaw`** (a law, taken
by `createHeaderFields`' proof; true after grpc's initializer, `Init.lean`). -/
abbrev grpc.outRawFn.law : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc ⊢
    globalAddr google_golang_org.grpc.metadataFromOutgoingContextRaw ↦□
      (functions google_golang_org.grpc.metadata.fromOutgoingContextRaw [] : GoFunc)

/-- **The law holds**: it is a conjunct of grpc's package fact (`grpcInit`, W1, 2026-11-26). -/
theorem grpc.outRawFn_law_holds : grpc.outRawFn.law (GF := GF) (hG := hG) := by
  iintro #Hpkg
  ihave #Hi : (_root_.Perennial.go_etcd_io.etcd.cache.v3.grpcInit (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hi with ⟨-, Hm, -⟩
  iexact Hm

end defs

end EtcdGrove
end Perennial
