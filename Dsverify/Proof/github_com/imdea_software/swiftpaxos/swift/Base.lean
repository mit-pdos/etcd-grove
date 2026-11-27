/-
The package fact of `github_com.imdea_software.swiftpaxos.swift` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `swift.pkgSt` (the lab's, Proof/swift/Pkg.lean): the hooks
`ExecHook`, `SyncHook`, `ReplyHook` are `nil` for good (test-only instrumentation; nothing in the
deployment writes them), `errVarintOverflow` is `errors.New(...)`'s error for good, `fastAckPool` is a
`sync.Pool` of owned `*MFastAck`s. The mutable globals `MaxDescRoutines` and `useFastAckPool` are in no
package fact: the first initialization hands them to the node's boot thread (`swift.mutGlobalsInit`).
Its initializer is not generated (notes/dsv-swiftpaxos.md, "Package initialization"): its proof is
hand-written.
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.swift
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.sync.PoolDefs
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.crypto.sha256.Link
public import Perennial.Proof.encoding.binary.Link
public import Dsverify.Proof.encoding.gob.Init
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.slices.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.bufio.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.config.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.hook.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Init
public import Dsverify.Proof.github_com.orcaman.concurrent_map.Base
public import Proof.encoding.json.Base
public import Net.Proof.net.rpc.PkgInit
public import Dsverify.Proof.os.signal.Init
public import Perennial.Proof.math.rand.Link
public import Dsverify.Proof.github_com.google.uuid.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `fastAckPool` holds: owned `*MFastAck`s. -/
def swift.fastAckP (x : GoAny) : IProp GF :=
  iprop(∃ (l : Loc) (fa : swift.MFastAck),
    ⌜x = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l⌝ ∗ l ↦ fa)

/-- **swift's package fact** (the file header). -/
def swift.pkgSt : IProp GF :=
  iprop(globalAddr swift.ExecHook ↦□ func.nil ∗ globalAddr swift.SyncHook ↦□ func.nil ∗
    globalAddr swift.ReplyHook ↦□ func.nil ∗
    errors.newVar swift.errVarintOverflow go!"binary: varint overflows a 64-bit integer" ∗
    (∃ f : GoFunc, sync.isPool (globalAddr swift.fastAckPool) f iprop(True) swift.fastAckP ∗ ⌜f ≠ func.nil⌝))

end facts

end github_com.imdea_software.swiftpaxos

namespace github_com.imdea_software.swiftpaxos.swift

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.swift :=
  define_is_pkg_init (github_com.imdea_software.swiftpaxos.swift.pkgSt (GF := GF))
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.swift :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.swift
end Perennial
