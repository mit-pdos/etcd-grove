/-
A server's registrations, and `RegisterName` (`server.go`), for the lab's `net/rpc` model.

* `svcReg s name rcvr` (persistent): server `s` has `rcvr` registered as `name`, for good: an
  element of the ghost map that `s`'s mutex invariant keeps equal to its `services` map
  (`isServerG`, `Base.lean`); Go refuses a second registration of a name, so the element never
  changes.
* `srvServes s W a` (persistent): every service `svc` that address `a` offers in `W`
  (`W.SS a svc = some S`) is registered at `s` with a receiver meeting `S` (`rcvrOk`): what the
  handler of `s` needs to serve a connection to `a`.
* `defaultSvcReg name rcvr`, `defaultServes W a`: the same for the `DefaultServer`.
* `RegisterName` (`Server.RegisterName` and the package's, on the `DefaultServer`): with the
  codec registered and the receiver one of the kit's (`RpcCodec.methods rcvr`), `nil` and the
  registration, or an error (the name is empty or taken, or `rcvr` has no methods).
* `Register` (`Server.Register` and the package's, on the `DefaultServer`): the same, under the
  name the codec's `Name` gives (`RpcNames.name rcvr`, with `kitNameOk`); also an error if that
  name is empty or does not start with an upper-case ASCII letter (Go: not exported).
-/
module

public import Harness.Proof.net.rpc.Codec
public import Perennial.Proof.errors.NewVar

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.rpc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit] [RpcCodec GF]

/-- Server `s` has `rcvr` registered as `name`, for good (persistent). -/
def svcReg (s : Loc) (name : GoString) (rcvr : GoInterface) : IProp GF :=
  iprop(∃ γ : GName, isServerG s γ ∗ ghostMapElem γ name .discard rcvr)

/-- Every service address `a` offers in `W` is registered at `s` with a receiver meeting its
spec (persistent). -/
def srvServes (s : Loc) (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(□ ∀ (svc : GoString) (S : MethodSpec GF), ⌜W.SS a svc = some S⌝ -∗
    ∃ rcvr : GoInterface, svcReg s svc rcvr ∗ rcvrOk rcvr S)

/-- The `DefaultServer` has `rcvr` registered as `name` (persistent). -/
def defaultSvcReg (name : GoString) (rcvr : GoInterface) : IProp GF :=
  iprop(∃ s : Loc, globalAddr DefaultServer ↦□ s ∗ svcReg s name rcvr)

/-- The `DefaultServer` serves every service of `a` in `W` (persistent). -/
def defaultServes (W : RpcWorld GF) (a : GoString) : IProp GF :=
  iprop(∃ s : Loc, globalAddr DefaultServer ↦□ s ∗ srvServes s W a)

instance svcReg_persistent (s : Loc) (name : GoString) (rcvr : GoInterface) :
    Persistent (svcReg (GF := GF) s name rcvr) := by
  unfold svcReg; infer_instance
instance srvServes_persistent (s : Loc) (W : RpcWorld GF) (a : GoString) :
    Persistent (srvServes (GF := GF) s W a) := by
  unfold srvServes; infer_instance
instance defaultSvcReg_persistent (name : GoString) (rcvr : GoInterface) :
    Persistent (defaultSvcReg (GF := GF) name rcvr) := by
  unfold defaultSvcReg; infer_instance
instance defaultServes_persistent (W : RpcWorld GF) (a : GoString) :
    Persistent (defaultServes (GF := GF) W a) := by
  unfold defaultServes; infer_instance

/-- A registration at the `DefaultServer` is one at the server it holds. -/
theorem defaultSvcReg_at (s : Loc) (name : GoString) (rcvr : GoInterface) :
    globalAddr DefaultServer ↦□ s ∗ defaultSvcReg (GF := GF) name rcvr ⊢ svcReg s name rcvr := by
  iintro ⟨#Hs, #Hd⟩
  unfold defaultSvcReg
  icases Hd with ⟨%s', #Hs', #Hr⟩
  icombine Hs Hs' gives %Heq
  subst Heq
  iexact Hr

/-- The `DefaultServer` serves `a` once each service of `a` is registered there with a receiver
meeting its spec. -/
theorem defaultServes_intro (W : RpcWorld GF) (a : GoString) :
    isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗
      (□ ∀ (svc : GoString) (S : MethodSpec GF), ⌜W.SS a svc = some S⌝ -∗
        ∃ rcvr : GoInterface, defaultSvcReg svc rcvr ∗ rcvrOk rcvr S) ⊢
      defaultServes W a := by
  iintro ⟨#Hpkg, #H⟩
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  icases HDefaultServer with ⟨%s, #Hs, -⟩
  unfold defaultServes srvServes
  iexists s
  iframe Hs
  imodintro
  iintro %svc %S %HS
  icases H $$ %svc %S %HS with ⟨%rcvr, #Hr, #Hok⟩
  iexists rcvr
  iframe Hok
  iapply defaultSvcReg_at s svc rcvr
  iframe Hs Hr

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit] [RpcCodec GF]

/-- `s.RegisterName(name, rcvr)`: see the file header. -/
abbrev Server.RegisterName.spec : Prop :=
  ∀ (s : Loc) (name : GoString) (rcvr : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isServer s ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ RpcCodec.methods rcvr }}
    (App (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"RegisterName")) (Val #name))
      (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg s name rcvr) ∨ ⌜err ≠ interface.nil⌝ }}

/-- `RegisterName(name, rcvr)` (on the `DefaultServer`): see the file header. -/
abbrev RegisterName.spec : Prop :=
  ∀ (name : GoString) (rcvr : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ RpcCodec.methods rcvr }}
    (App (App (Val (@! net.rpc.RegisterName)) (Val #name)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ defaultSvcReg name rcvr) ∨ ⌜err ≠ interface.nil⌝ }}

set_option goose.wp.extras true

theorem Server.RegisterName.wp_proof : Server.RegisterName.spec (GF := GF) (hG := hG) := by
  intro s name rcvr
  wp_start as ⟨#Hsrv, #Hset, #Hok, Hm⟩
  ihave ⟨-, #Hsync, -, #Herrors⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
  unfold codecFns
  icases Hfns with ⟨#HfE, #HfD, #HfM, #HfC, -⟩
  unfold kitCodecOk
  icases Hok with ⟨-, -, #HmOk, -⟩
  unfold methodsOk
  wp_auto
  wp_apply HmOk $$ [$Hm] as %n
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  unfold isServer
  icases Hsrv with ⟨%γ, #Hsg⟩
  ihave #Hsg' := Hsg
  unfold isServerG
  iNamed Hsg'
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (∃ m : GMap GoString GoInterface, ownMap mp (DFrac.own 1) m ∗
    ghostMapAuth γ 1 m : IProp GF) $$ [Hinv]
  · unfold servicesInv; iexact Hinv
  icases Hinv with ⟨%m, Hmap, Hauth⟩
  wp_apply (wp_map_lookup2 go.string (go.InterfaceType []) mp m name (DFrac.own 1)) $$ Hmap
    as Hmap
  rcases hm : m !! name with _ | r0
  · simp only [Option.isSome_none]
    wp_auto
    wp_apply (wp_mapInsert go.string mp m name rcvr) $$ Hmap as Hmap
    imod ghost_map_insert_persist name rcvr (by rw [← gmap_get?_eq]; exact hm) $$ Hauth
      with ⟨Hauth, #Hel⟩
    wp_apply sync.Mutex.Unlock.wp_proof _ (servicesInv mp γ) $$ [$Hsync $Hmu $Hlocked Hmap Hauth]
    · unfold servicesInv; iexists _; iframe Hmap Hauth
    iapply HΦ; ileft; isplitr
    · ipureintro; rfl
    unfold svcReg
    iexists γ; iframe Hel; unfold isServerG; iexact Hsg
  · simp only [Option.isSome_some, _root_.decide_true]
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof _ (servicesInv mp γ) $$ [$Hsync $Hmu $Hlocked Hmap Hauth]
    · unfold servicesInv; iexists _; iframe Hmap Hauth
    wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]

theorem RegisterName.wp_proof : RegisterName.spec (GF := GF) (hG := hG) := by
  intro name rcvr
  wp_start as ⟨#Hset, #Hok, Hm⟩
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  icases HDefaultServer with ⟨%s, #Hs, #Hsrv⟩
  wp_auto
  wp_apply Server.RegisterName.wp_proof $$ [$Hpkg $Hsrv $Hset $Hok $Hm] as %err Hr
  iapply HΦ
  icases Hr with (⟨%He, #Hr⟩ | %He)
  · ileft; isplitr
    · ipureintro; exact He
    unfold defaultSvcReg; iexists s; iframe Hs Hr
  · iright; ipureintro; exact He

end spec

section register
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions] [RpcKit] [RpcCodec GF]
variable [RpcNames]

/-- `s.Register(rcvr)`: see the file header. -/
abbrev Server.Register.spec : Prop :=
  ∀ (s : Loc) (rcvr : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isServer s ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ kitNameOk (GF := GF) ∗ RpcCodec.methods rcvr }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"Register")) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ svcReg s (RpcNames.name rcvr) rcvr) ∨ ⌜err ≠ interface.nil⌝ }}

/-- `Register(rcvr)` (on the `DefaultServer`): see the file header. -/
abbrev Register.spec : Prop :=
  ∀ (rcvr : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ codecSet (GF := GF) ∗
      kitCodecOk (GF := GF) ∗ kitNameOk (GF := GF) ∗ RpcCodec.methods rcvr }}
    (App (Val (@! net.rpc.Register)) (Val #rcvr))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ defaultSvcReg (RpcNames.name rcvr) rcvr) ∨
        ⌜err ≠ interface.nil⌝ }}

set_option goose.wp.extras true

theorem Server.Register.wp_proof : Server.Register.spec (GF := GF) (hG := hG) := by
  intro s rcvr
  wp_start as ⟨#Hsrv, #Hset, #Hok, #Hname, Hm⟩
  ihave ⟨-, -, -, #Herrors⟩ := deps_of_pkg $$ Hpkg
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
  unfold codecFns
  icases Hfns with ⟨-, -, -, -, #HfN⟩
  wp_auto
  unfold kitNameOk nameOk
  wp_apply Hname
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  rcases hn : RpcNames.name rcvr with _ | ⟨b0, rest⟩
  · exact absurd hn Hif
  simp only [List.getElem?_cons_zero]
  wp_auto
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  wp_if_destruct
  · wp_apply errors.wp_New_errorString as %x #-
    iapply HΦ; iright; ipureintro; simp [interface.mkOk]
  wp_apply Server.RegisterName.wp_proof $$ [$Hpkg $Hsrv $Hset $Hok $Hm] as %err Hr
  iapply HΦ
  iexact Hr

theorem Register.wp_proof : Register.spec (GF := GF) (hG := hG) := by
  intro rcvr
  wp_start as ⟨#Hset, #Hok, #Hname, Hm⟩
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  icases HDefaultServer with ⟨%s, #Hs, #Hsrv⟩
  wp_auto
  wp_apply Server.Register.wp_proof $$ [$Hpkg $Hsrv $Hset $Hok $Hname $Hm] as %err Hr
  iapply HΦ
  icases Hr with (⟨%He, #Hr⟩ | %He)
  · ileft; isplitr
    · ipureintro; exact He
    unfold defaultSvcReg; iexists s; iframe Hs Hr
  · iright; ipureintro; exact He

end register

end net.rpc

end Perennial
