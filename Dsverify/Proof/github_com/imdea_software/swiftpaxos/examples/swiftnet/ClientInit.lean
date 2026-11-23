/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientInit.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The test package's initialization (`examples/swiftnet`'s `initialize'`, stage 2: it imports the
harness's `remote`, initialized by `remote.wp_initialize'`): it initializes every
imported package, then has no state of its own (`isPkgInit` is `True` for it). The harness's and
Perennial's packages use their proved initializers; SwiftPaxos's packages (`client`, `config`,
`dlog`, `master`, `replica/defs`, `swift`, `state`) and the lab's `encoding/gob` model use
their initializers' specs (`InitSpec`), hypotheses here: their packages own them.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface

-- PORT: lab imports dropped: Harness.Remote.Init, Harness.Proof.net.rpc.initialize, Harness.Proof.net.http.initialize, Harness.Proof.net.initialize, Harness.Proof.math.rand, Harness.Proof.bufio.Base, Harness.CheckerSpec, Harness.WriteOnceChecker

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace adapter

section init
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

/-- A package's initializer's spec (the form of Perennial's `X.initialize'.spec`). -/
abbrev InitSpec (pkg : GoString) [IsPkgInit (IProp netDistGF) pkg]
    [GetIsPkgInitWf (IProp netDistGF) pkg] (init : val) : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp netDistGF),
  GetIsPkgInitProp pkg get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val init) (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp netDistGF) pkg }}

/-- The initializers of the SwiftPaxos packages and of the `encoding/gob` model that the test
package imports (their packages' proofs). -/
structure SwiftInits : Prop where
  client : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.client client.initialize'
  config : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.config config.initialize'
  dlog : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.dlog dlog.initialize'
  master : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.master master.initialize'
  defs : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.replica.defs
    replica.defs.initialize'
  swift : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.swift swift.initialize'
  state : InitSpec pkg_id.github_com.imdea_software.swiftpaxos.state state.initialize'
  gob : InitSpec pkg_id.encoding.gob encoding.gob.initialize'

set_option goose.wp.extras true

theorem initialize.wp_proof (I : SwiftInits) :
    InitSpec pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet
      examples.swiftnet.initialize' := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  have wp_io := io.wp_initialize' (GF := netDistGF) (hG := hG)
  have wp_errors := errors.wp_initialize' (GF := netDistGF) (hG := hG)
  have wp_time := time.wp_initialize' (GF := netDistGF) (hG := hG)
  have wp_sync := sync.wp_initialize' (GF := netDistGF) (hG := hG)
  have wp_net := net.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_time wp_io
  have wp_bufio := bufio.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_io wp_errors
  have wp_http := net.http.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_sync wp_net
    wp_errors wp_bufio
  have wp_rpc := net.rpc.initialize'.wp_proof (GF := netDistGF) (hG := hG) wp_http wp_sync wp_net
    wp_errors
  wp_apply I.gob _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_gob⟩
  wp_apply I.state _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_state⟩
  wp_apply wp_errors _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_errors⟩
  wp_apply remote.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_remote⟩
  wp_apply check.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_check⟩
  wp_apply I.swift _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_swift⟩
  wp_apply I.defs _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_defs⟩
  wp_apply I.master _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_master⟩
  wp_apply I.dlog _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_dlog⟩
  wp_apply I.config _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_config⟩
  wp_apply I.client _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_client⟩
  wp_apply models.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_models⟩
  wp_apply wp_time _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_time⟩
  wp_apply wp_sync _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_sync⟩
  wp_apply strings.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_strings⟩
  wp_apply wp_rpc _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_rpc⟩
  wp_apply wp_http _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_http⟩
  wp_apply wp_net _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #H_net⟩
  wp_apply math.rand.initialize'.wp_proof _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H_rand⟩
  wp_apply log.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H_log⟩
  wp_apply wp_io _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H_io⟩
  wp_apply fmt.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H_fmt⟩
  iframe Hown
  is_pkg_init_finish

end init

end adapter

end Perennial.github_com.imdea_software.swiftpaxos
