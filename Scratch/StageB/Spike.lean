/-
Stage B0 spike (3) (scope-r5 §3.4, A4-MAJ-3): the adapter, exactly as stated: from a handler's
`grpcMethodOkMd` at a three-pool bundle `R₁ ∗ R₂ ∗ R₃` (abstract `IProp`s: no `Timeless`, so the
abstract `E.RD` is covered) and the three pools' handles at levels 1, 2, 3, the run contract
`grpcRunOkMd` (the fork's `threadTok ∗ £ 1` in, `threadTok` out). Scratch: not built by `lake build`,
never landed.
-/
module

public import Proof.google_golang_org.grpc.InvGrpc
public import Perennial.Proof.ThreadPool

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section spike
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The run contract** (r5 §2.1, B1a's `grpcRunOkMd`): `grpcMethodOkMd`'s text with the pre's `S`
replaced by `threadTok ∗ £ 1` and the post's by `threadTok`. -/
def spikeRunOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ threadTok ∗ £ 1 ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
        grpcSrvChain ics ui ∗ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); threadTok ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        (⌜err ≠ GoInterface.nil ∧ go_etcd_io.etcd.cache.v3.errDesc err ∈ handlerDescs⌝ -∗
          Ψe (go_etcd_io.etcd.cache.v3.errDesc err)) ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})

/-- Levels 1, 2, 3 of a thread token, and the rest. -/
theorem spike_threadTok_123 (HT : 4 ≤ threadBound GF) :
    threadTok (GF := GF) ⊣⊢ levelTok 0 ∗ levelTok 1 ∗ levelTok 2 ∗ levelTok 3 ∗ threadTokFrom 4 := by
  constructor
  · iintro H
    icases (threadTok_level0 (GF := GF)).1 $$ H with ⟨H0, H⟩
    icases (threadTokFrom_succ (GF := GF) 1 (by omega)).1 $$ H with ⟨H1, H⟩
    icases (threadTokFrom_succ (GF := GF) 2 (by omega)).1 $$ H with ⟨H2, H⟩
    icases (threadTokFrom_succ (GF := GF) 3 (by omega)).1 $$ H with ⟨H3, H⟩
    iframe
  · iintro ⟨H0, H1, H2, H3, H4⟩
    iapply (threadTok_level0 (GF := GF)).2
    iframe H0
    iapply (threadTokFrom_succ (GF := GF) 1 (by omega)).2
    iframe H1
    iapply (threadTokFrom_succ (GF := GF) 2 (by omega)).2
    iframe H2
    iapply (threadTokFrom_succ (GF := GF) 3 (by omega)).2
    iframe

/-- **The adapter** (A4-MAJ-3, form (b)): one later credit strips the three pools' laters. -/
theorem spike_runOk_of_pools {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep) (R₁ R₂ R₃ : IProp GF)
    (N₁ N₂ N₃ : Namespace) (γ₁ γ₂ γ₃ : GName) (HT : 4 ≤ threadBound GF) :
    □ grpcMethodOkMd mh srv ics iprop(R₁ ∗ R₂ ∗ R₃) Spec ∗
      threadPool.isThreadPoolL N₁ 1 γ₁ R₁ ∗ threadPool.isThreadPoolL N₂ 2 γ₂ R₂ ∗
      threadPool.isThreadPoolL N₃ 3 γ₃ R₃ ⊢
    spikeRunOkMd mh srv ics Spec := by
  iintro ⟨#Hm, #Hp1, #Hp2, #Hp3⟩
  iunfold grpcMethodOkMd at Hm
  unfold spikeRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨Htok, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  icases (spike_threadTok_123 (GF := GF) HT).1 $$ Htok with ⟨H0, H1, H2, H3, H4⟩
  imod threadPool.borrowL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 H1] with ⟨HR1, Hl1⟩
  · iframe; iframe #
  imod threadPool.borrowL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 H2] with ⟨HR2, Hl2⟩
  · iframe; iframe #
  imod threadPool.borrowL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 H3] with ⟨HR3, Hl3⟩
  · iframe; iframe #
  ihave HR : iprop(▷ (R₁ ∗ R₂ ∗ R₃)) $$ [HR1 HR2 HR3]
  · inext; iframe
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc HR with HR
  iapply wp_fupd
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HR Hctx Hrc Hd Hch HSpec]
  · iframe
  inext
  iintro %resp %err ⟨⟨HB1, HB2, HB3⟩, Hok, Herr, Hsrv⟩
  imod threadPool.giveBackL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 Hl1 HB1] with H1
  · iframe; iframe #
  imod threadPool.giveBackL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 Hl2 HB2] with H2
  · iframe; iframe #
  imod threadPool.giveBackL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 Hl3 HB3] with H3
  · iframe; iframe #
  imodintro
  iapply HΨ
  iframe
  iapply (spike_threadTok_123 (GF := GF) HT).2
  iframe

end spike


/-! ## Spike (1)-(2): the carrier on toy axioms -/

section pure
variable [GooseExts]

/-- (r5 §2.1) Go's configuration of one server. -/
structure SpikeCfg (GF : BundledGFunctors) where
  ics : List GoFunc
  sics : List GoFunc
  regs : List (GoString × val × GoInterface)
  sregs : List (GoString × val × GoInterface)

theorem spike_inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: l, h, x, hx, y, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd hxy.symm (h.1 y hy')
    · exact absurd hxy (h.1 x hx')
    · exact spike_inj_of_nodup_map f l h.2 x hx' y hy' hxy

/-- (1) pure: under the joint `Nodup`, two entries of one name in `regs` are one entry. -/
theorem spike_regs_unique (regs sregs : List (GoString × val × GoInterface)) (name : GoString)
    (mh mh' : val) (srv srv' : GoInterface)
    (Hnd : ((regs ++ sregs).map Prod.fst).Nodup)
    (H1 : (name, mh, srv) ∈ regs) (H2 : (name, mh', srv') ∈ regs) : mh = mh' ∧ srv = srv' := by
  have Hnd' : (regs.map Prod.fst).Nodup := by
    rw [List.map_append] at Hnd; exact (List.nodup_append.mp Hnd).1
  have := spike_inj_of_nodup_map Prod.fst regs Hnd' _ H1 _ H2 rfl
  simp only [Prod.mk.injEq, true_and] at this
  exact this

end pure

section spike
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Toy `grpcSrvCfgRaw` (an axiom constant, A4-MIN-7). -/
axiom spikeCfgRaw (γ : GName) (c : SpikeCfg GF) : IProp GF
def spikeCfgIs (γ : GName) (c : SpikeCfg GF) : IProp GF := iprop(□ spikeCfgRaw γ c)
instance spikeCfgIs_persistent (γ : GName) (c : SpikeCfg GF) : Persistent (spikeCfgIs γ c) := by
  unfold spikeCfgIs; infer_instance
/-- Toy `grpcSrvCfg_agree`. -/
axiom spikeCfg_agree (γ : GName) (c c' : SpikeCfg GF) :
  spikeCfgIs (GF := GF) γ c ∗ spikeCfgIs γ c' ⊢ ⌜c = c'⌝

/-- Toy `isGrpcRpcAt`. -/
def spikeRpcAt {Req Rep : ProtoMsg GF} (γ : GName) (name : GoString) (Spec : GrpcSpecMd Req Rep) :
    IProp GF :=
  iprop(∃ (c : SpikeCfg GF) (mh : val) (srv : GoInterface),
    spikeCfgIs γ c ∗ ⌜(name, mh, srv) ∈ c.regs⌝ ∗ □ spikeRunOkMd mh srv c.ics Spec)

/-- Toy `grpcAccepted`'s unary arm: the deposit packaged with `∃ (Req Rep : ProtoMsgT GF)`. -/
def spikeAccepted (γ : GName) (c : SpikeCfg GF) (rmh : val) (rsrv : GoInterface) (ci : GoInterfaceOk) :
    IProp GF :=
  iprop(∃ (name : GoString) (Req Rep : ProtoMsgT GF)
      (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M) (Φ : Rep.M → IProp GF)
      (Ψe : GoString → IProp GF),
    ⌜(name, rmh, rsrv) ∈ c.regs⌝ ∗ spikeRpcAt γ name Spec ∗
    ▷ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe)

/-- (1) The carrier's identification: the deposited contract is about Go's handler `rmh`. -/
theorem spike_carrier_ident (γ : GName) (c : SpikeCfg GF) (rmh : val) (rsrv : GoInterface)
    (ci : GoInterfaceOk) (Hnd : ((c.regs ++ c.sregs).map Prod.fst).Nodup) :
    spikeCfgIs γ c ∗ spikeAccepted γ c rmh rsrv ci ⊢
      ∃ (Req Rep : ProtoMsgT GF) (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M)
        (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF),
        □ spikeRunOkMd rmh rsrv c.ics Spec ∗ ▷ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe := by
  iintro ⟨#Hc, Hacc⟩
  iunfold spikeAccepted at Hacc
  icases Hacc with ⟨%name, %Req, %Rep, %Spec, %m, %Φ, %Ψe, %Hin, Hat, HSpec⟩
  iunfold spikeRpcAt at Hat
  icases Hat with ⟨%c', %mh, %srv, #Hc', %Hin', #Hrun⟩
  ihave %Heq := spikeCfg_agree γ c c' $$ [Hc Hc']
  · iframe #
  subst Heq
  obtain ⟨rfl, rfl⟩ := spike_regs_unique c.regs c.sregs name rmh mh rsrv srv Hnd Hin Hin'
  iexists Req, Rep, Spec, m, Φ, Ψe
  iframe #
  iframe

/-- A model-only name (r5 §2.2, m2: `#` cannot occur in a Go import path). -/
abbrev spikeLeafName : GoString := go!"google.golang.org/grpc#model.leaf"

/-- Toy leaf axiom on the model-only name (no `FuncUnfold` exists for it). -/
axiom spikeLeaf_spec :
  {{ (iprop(True) : IProp GF) }} (App (Val (@! spikeLeafName)) (Val #())) {{ RET #(); True }}

/-- (2) The carrier's fork: the body gets the fork's token and credit; the run calls the leaf through
`FuncResolve` (as goose's code does) and exits with the token. -/
theorem spike_fork_leaf (P : IProp GF) :
    □ (threadTok -∗ £ 1 -∗ P -∗ WP (App (App (Val (GoInstruction (FuncResolve spikeLeafName [])))
        (Val #())) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) ∗
    P ⊢ WP (Fork (App (App (Val (GoInstruction (FuncResolve spikeLeafName []))) (Val #())) (Val #())))
      {{ v, True }} := by
  iintro ⟨#Hbody, HP⟩
  iapply wp_fork_tok_upd
  inext
  iintro Htok Hlc
  imodintro
  isplitl [Htok Hlc HP]
  · iapply Hbody $$ Htok Hlc HP
  · ipureintro; trivial

/-- (2') The body itself, over the leaf axiom. -/
theorem spike_body :
    ⊢ □ (threadTok -∗ £ 1 -∗ iprop(True) -∗ WP (App (App (Val (GoInstruction (FuncResolve spikeLeafName [])))
        (Val #())) (Val #())) {{ v, ⌜v.isPanic = false⌝ ∗ threadTok }}) := by
  imodintro
  iintro Htok _ _
  wp_auto
  wp_apply spikeLeaf_spec
  iframe
  ipureintro; exact isPanic_intoVal ()

end spike

end EtcdGrove
end Perennial
