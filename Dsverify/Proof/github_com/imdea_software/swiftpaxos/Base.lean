/-
The swiftpaxos kit's common base (notes/dsv-swiftpaxos.md), in place of the lab's generated
`SwiftNetSpec.lean` (dsverify-lab examples/swiftpaxos/proof, run swift-n2nofast-1) and its
`Harness/SafeDistSha.lean`:

* the extension list of the kit's machines, `netShaExts`: this repository's net extension
  (`Net.netExt`) and Perennial's SHA-256 extension with `sha256NoCollisionFilter` (a hash step that
  would return the hash of another input hashed before is an `AngelicExit`), with its semantics,
  ghost state and `HasExt`/`HasSha256` instances, under the lab's names (namespace `Dsv`), so the
  lab's files keep their `attribute [local instance] netShaExts ...` lines. (`Net/Statement`'s
  bridge is for `[netExt]` alone: `notes/dsv-swiftpaxos.md`, "Design findings".)
* `SwiftNetPkgState`: the libraries' representation hypotheses (`SwiftLibs`). The packages'
  post-initialization facts are their `Base.lean` instances, imported here (the lab's
  `SwiftNetPkgState` held them as a run-level choice).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.examples.swiftnet
public import GooseLang.Ext.Net.Adequacy
public import GooseLang.Ext.Net.Proto
public import Perennial.GooseLang.Ext.Sha256.Specs
public import Perennial.Proof.crypto.sha256
public import Dsverify.GeneratedProof.github_com.emirpasic.gods.utils
public import Dsverify.GeneratedProof.github_com.google.uuid
public import Dsverify.GeneratedProof.os.signal
public import Net.Proof.net.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Wire
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Proof.net.url.PkgInit
public import Proof.os.PkgInit
public import Proof.bufio.PkgInit
public import Proof.syscall.PkgInit
public import Proof.math.rand.Base
public import Dsverify.Proof.github_com.emirpasic.gods.utils.Base
public import Dsverify.Proof.github_com.emirpasic.gods.containers.Base
public import Dsverify.Proof.github_com.emirpasic.gods.maps.Base
public import Dsverify.Proof.github_com.emirpasic.gods.trees.Base
public import Dsverify.Proof.github_com.emirpasic.gods.trees.redblacktree.Base
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Base
public import Proof.encoding.json.Base
public import Dsverify.Proof.encoding.gob.Init
public import Dsverify.Proof.github_com.google.uuid.Init
public import Dsverify.Proof.os.signal.Init
public import Net.Proof.net.rpc.PkgInit
public import Net.Proof.net.http.PkgInit
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.config.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.hook.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Proof.unicode.utf8.Base
public import Proof.internal.poll.PkgInit
public import Perennial.Proof.log
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.io
public import Perennial.Proof.bytes
public import Perennial.Proof.context
public import Perennial.Proof.reflect
public import Perennial.Proof.slices
public import Perennial.Proof.strings
public import Perennial.Proof.fmt
public import Perennial.Proof.errors
public import Perennial.Proof.strconv
public import Perennial.Proof.sort
public import Perennial.Proof.math
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.runtime
public import Perennial.Proof.math.bits

@[expose] public section

noncomputable section

namespace Perennial

namespace Dsv

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-! ## The extension list: TCP and SHA-256 -/

/-- The extensions of the kit's machines: TCP, and SHA-256 with `sha256NoCollisionFilter`. -/
@[reducible] def netShaExts : GooseExts := ⟨[netExt, sha256Ext sha256NoCollisionFilter]⟩

/-- The semantics of `netShaExts`. -/
@[reducible] def netShaExtsSemantics : @GooseSemantics netShaExts :=
  letI := netShaExts
  ⟨(net_semantics, sha256_semantics sha256NoCollisionFilter, ⟨⟩)⟩

/-- The ghost state of `netShaExts`. -/
@[reducible] def netShaExtsInterp : @GooseInterp netShaExts :=
  letI := netShaExts
  ⟨(net_interp, sha256_interp sha256NoCollisionFilter, ⟨⟩)⟩

set_option linter.defProp false in
/-- `netShaExts` has the TCP extension. -/
@[reducible] def netShaExts_has :
    @HasExt netShaExts netShaExtsSemantics netShaExtsInterp netExt _ _ :=
  letI := netShaExts; letI := netShaExtsSemantics; letI := netShaExtsInterp
  { registered := rfl, sem_eq := rfl, interp_eq := rfl }

set_option linter.defProp false in
/-- `netShaExts` has the SHA-256 extension. -/
@[reducible] def netShaExts_hasSha :
    @HasExt netShaExts netShaExtsSemantics netShaExtsInterp (sha256Ext sha256NoCollisionFilter) _ _ :=
  letI := netShaExts; letI := netShaExtsSemantics; letI := netShaExtsInterp
  { registered := rfl, sem_eq := rfl, interp_eq := rfl }

/-- The kit's SHA-256 extension has the filter `sha256NoCollisionFilter`. -/
theorem netShaExts_hasSha256 :
    @HasSha256 netShaExts netShaExtsSemantics netShaExtsInterp sha256NoCollisionFilter :=
  letI := netShaExts; letI := netShaExtsSemantics; letI := netShaExtsInterp
  ⟨netShaExts_hasSha⟩

/-- Collision resistance holds of the filter (Perennial's). -/
theorem netSha_noCollision : Sha256NoCollision sha256NoCollisionFilter :=
  sha256NoCollisionFilter_noCollision

section gf
attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

/-- The ghost state of a machine of the deployment (the lab's `netDistGF`): remote's `remoteGF`
(`Net`'s `netGF` with iris-lean's non-atomic invariants at slot 8, which remote's `Check` needs,
`NaInvG`) over the values of `netShaExts` (the heap's and the prophecies' slots name `val`, which
depends on the extension list, so `remoteGF`, over `netExts`'s, does not do), whose universal slot
holds the ghost state of both extensions. -/
def netDistGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | 8 => ⟨NaInvF, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- `netDistGF`'s slots for `netShaExts`: both extensions' ghost state in the universal slot 0. -/
instance netShaGpreS : GooseGpreS netDistGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨allGOfSlot 0 rfl⟩, allGOfSlot 0 rfl, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

/-- Its non-atomic invariants (remote's `Check`). -/
instance netDistGF_naInvG : NaInvG netDistGF := ⟨⟨8, rfl⟩⟩

end gf

end Dsv

namespace net.rpc

open Iris Iris.BI

/-- The kit's codec, as the specs see it (the lab's `RpcCodec`; `lib/NetRpc.lean`). -/
class RpcCodec [GooseExts] (GF : BundledGFunctors) where
  enc : GoInterface → (List w8 → IProp GF) → IProp GF
  dec : List w8 → GoInterface → (Bool → IProp GF) → IProp GF
  call : GoInterface → GoString → List w8 → (List w8 → GoString → Bool → IProp GF) → IProp GF
  methods : GoInterface → IProp GF
  /-- the receivers' representations (`Net/`'s `CodecSpec.rcv`, the net/rpc server's) -/
  rcv : GoInterface → (Loc → IProp GF) → IProp GF

end net.rpc

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

namespace github_com.imdea_software.swiftpaxos

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **The libraries' representation predicates, hypotheses** (notes/dsv-swiftpaxos.md,
"Hypotheses"): the predicates the specs of the libraries without a proved model here are stated
over, with the laws the proof uses of them, each named after the lab's definition or lemma (the
lab proved them over its own models). A deployment's proof is given them, with their specs
(`SwiftHyps`), and proves `swiftpaxos_remote_robust` for any choice. -/
class SwiftLibs (GF : BundledGFunctors) extends Net.NetProtoGS where
  /-- The real `encoding/gob`'s format (Spec/swift/Wire.lean, `sp.GobFmt`): the instance
  `swiftGobFmt` below. -/
  gobFmt : sp.GobFmt
  /-- A fresh `*gob.Encoder` at `enc` writing to `w` (Spec/encoding/gob/Defs.lean; the lab's
  model's `enc ↦ Encoder{w}`). The format it writes is the parent `sp.GobFmt`'s. -/
  gobEncoder : HeapGS HasLC.hasLC GF → Loc → GoInterface → IProp GF
  /-- A fresh `*gob.Decoder` at `dec` reading `r` directly (the lab's model's `dec ↦ Decoder{r}`). -/
  gobDecoder : HeapGS HasLC.hasLC GF → Loc → GoInterface → IProp GF

/-- gob's format from the libraries at the deployment's ghost state: an instance with `GF` fixed
(an instance through a parent projection would leave `GF` undetermined, which instance search
does not solve). -/
instance swiftGobFmt [l : SwiftLibs Dsv.netDistGF] : sp.GobFmt := l.gobFmt

/-- The lab's `SwiftNetPkgState`, here only the libraries' representation hypotheses (`SwiftLibs`):
each package's post-initialization fact is its own `IsPkgInit` instance, in its `Base.lean`
(`Dsverify/Proof/<package>/Base.lean`, imported above; the lab's run-level choice `pkgStates` gave
them as fields). Kept as a class so the ported proofs' `[SwiftNetPkgState GF]` binders stand. -/
class SwiftNetPkgState (GF : BundledGFunctors) extends SwiftLibs GF

/-- A choice of `SwiftNetPkgState` at every heap. -/
abbrev SwiftNetPkgStates [GoGlobalContext] :=
  ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics], SwiftNetPkgState GF

end defs

end github_com.imdea_software.swiftpaxos

end Perennial
