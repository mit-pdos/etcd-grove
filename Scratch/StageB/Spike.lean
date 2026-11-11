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
public import Proof.google_golang_org.grpc.InvGrpcServer

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

/-! ## Spike (4): the joint `Nodup` on etcd's server path (M2 (3)) -/

namespace Perennial
namespace EtcdGrove

section nodup
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

theorem spike_go_slash : (go!"/" : GoString) = [(47 : w8)] := rfl

theorem spike_sep_inj {α : Type} (c : α) : ∀ (a a' b b' : List α), c ∉ a → c ∉ a' →
    a ++ c :: b = a' ++ c :: b' → a = a' ∧ b = b'
  | [], [], b, b', _, _, h => by simpa using h
  | [], x :: a', b, b', _, h2, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) h2
  | x :: a, [], b, b', h1, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1.symm ▸ List.mem_cons_self) h1
  | x :: a, y :: a', b, b', h1, h2, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have := spike_sep_inj c a a' b b' (fun hm => h1 (List.mem_cons_of_mem _ hm))
      (fun hm => h2 (List.mem_cons_of_mem _ hm)) h
    exact ⟨by rw [this.1], this.2⟩

/-- **`grpcFullName_inj`** (r5 §2.4): slash-free service names are recovered from full names. -/
theorem spike_grpcFullName_inj (sn sn' mn mn' : GoString) (h1 : (47 : w8) ∉ sn) (h2 : (47 : w8) ∉ sn')
    (h : grpcFullName sn mn = grpcFullName sn' mn') : sn = sn' ∧ mn = mn' := by
  unfold grpcFullName at h
  rw [spike_go_slash] at h
  simp only [List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq, true_and] at h
  exact spike_sep_inj (47 : w8) sn sn' mn mn' h1 h2 h

theorem spike_nodup_map_on {α β : Type} (f : α → β) : ∀ (l : List α),
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, spike_nodup_map_on f l
      (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)) hnd.2⟩
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact hnd.1 (hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb ▸ hb)

/-- The services' full names: service `s.1`'s methods `s.2.1` and streams `s.2.2`. -/
def spikeNames (S : List (GoString × List GoString × List GoString)) : List GoString :=
  S.flatMap fun s => (s.2.1 ++ s.2.2).map (grpcFullName s.1)

/-- Distinct slash-free services with per-service distinct names have distinct full names. -/
theorem spike_names_nodup (S : List (GoString × List GoString × List GoString))
    (hS : ∀ s ∈ S, (47 : w8) ∉ s.1 ∧ (s.2.1 ++ s.2.2).Nodup) (hsn : (S.map (·.1)).Nodup) :
    (spikeNames S).Nodup := by
  induction S with
  | nil => simp [spikeNames]
  | cons s S ih =>
    simp only [spikeNames, List.flatMap_cons, List.map_cons, List.nodup_cons] at hsn ⊢
    have hs := hS s List.mem_cons_self
    refine List.nodup_append.mpr ⟨?_, ih (fun t ht => hS t (List.mem_cons_of_mem _ ht)) hsn.2, ?_⟩
    · refine spike_nodup_map_on _ _ ?_ hs.2
      intro x _ y _ hxy
      exact (spike_grpcFullName_inj s.1 s.1 x y hs.1 hs.1 hxy).2
    · intro a ha b hb hab
      subst hab
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨t, ht, hb⟩ := List.mem_flatMap.mp hb
      obtain ⟨y, _, hy⟩ := List.mem_map.mp hb
      have := (spike_grpcFullName_inj s.1 t.1 x y hs.1 (hS t (List.mem_cons_of_mem _ ht)).1 hy.symm).1
      exact hsn.1 (this ▸ List.mem_map_of_mem ht)

end nodup

end EtcdGrove
end Perennial

/-! ### Spike (4b): etcd's lists, in `v3rpc.Server`'s registration order -/

namespace Perennial
namespace EtcdGrove

section nodupEtcd
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]

open google_golang_org.grpc in
theorem spike_descRegs_names (sn : GoString) (mds : List MethodDesc) (ss : GoInterface) :
    (descRegs sn mds ss).map Prod.fst = (mds.map (·.MethodName')).map (grpcFullName sn) := by
  simp [descRegs, List.map_map, Function.comp_def]

open google_golang_org.grpc in
theorem spike_descSRegs_names (sn : GoString) (sds : List StreamDesc) (ss : GoInterface) :
    (descSRegs sn sds ss).map Prod.fst = (sds.map (·.StreamName')).map (grpcFullName sn) := by
  simp [descSRegs, List.map_map, Function.comp_def]

theorem spike_health_prefix : (go!"/grpc.health.v1.Health/" : GoString) =
    go!"/" ++ go!"grpc.health.v1.Health" ++ go!"/" := rfl

open google_golang_org.grpc in
/-- **The joint `Nodup` of `v3rpc.Server`'s registrations** (M2 (3)), from what `svcDescsOk` gives
(the KV, Watch, Lease, Auth names exactly; Cluster's and Maintenance's `descNames` distinct) and the
restated `RegisterHealthServer` post (`rs ++ srs` distinct, under `/grpc.health.v1.Health/`), in the
proof's registration order (KV, Watch, Lease, Cluster, Auth, health, Maintenance). -/
theorem spike_v3rpc_nodup (kmds lmds cmds amds mmds : List MethodDesc)
    (ksds wsds lsds csds asds msds : List StreamDesc) (q pw ql pc pa pm : GoInterface)
    (rs srs : List (GoString × val × GoInterface))
    (hk : kmds.map (·.MethodName') = [go!"Range", go!"Put", go!"DeleteRange", go!"Txn", go!"Compact"])
    (hks : ksds.map (·.StreamName') = [go!"RangeStream"])
    (hws : wsds.map (·.StreamName') = [go!"Watch"])
    (hl : lmds.map (·.MethodName') = [go!"LeaseGrant", go!"LeaseRevoke", go!"LeaseTimeToLive", go!"LeaseLeases"])
    (hls : lsds.map (·.StreamName') = [go!"LeaseKeepAlive"])
    (hc : (descNames cmds csds).Nodup)
    (ha : (amds.map (·.MethodName')).Nodup) (has : asds.map (·.StreamName') = [])
    (hm : (descNames mmds msds).Nodup)
    (hH : ((rs ++ srs).map Prod.fst).Nodup)
    (hHp : ∀ x ∈ rs ++ srs, go!"/grpc.health.v1.Health/" <+: x.1) :
    let regs := [] ++ descRegs go!"etcdserverpb.KV" kmds q ++ descRegs go!"etcdserverpb.Watch" [] pw ++
      descRegs go!"etcdserverpb.Lease" lmds ql ++ descRegs go!"etcdserverpb.Cluster" cmds pc ++
      descRegs go!"etcdserverpb.Auth" amds pa ++ rs ++ descRegs go!"etcdserverpb.Maintenance" mmds pm
    let sregs := [] ++ descSRegs go!"etcdserverpb.KV" ksds q ++ descSRegs go!"etcdserverpb.Watch" wsds pw ++
      descSRegs go!"etcdserverpb.Lease" lsds ql ++ descSRegs go!"etcdserverpb.Cluster" csds pc ++
      descSRegs go!"etcdserverpb.Auth" asds pa ++ srs ++ descSRegs go!"etcdserverpb.Maintenance" msds pm
    ((regs ++ sregs).map Prod.fst).Nodup := by
  intro regs sregs
  let S : List (GoString × List GoString × List GoString) :=
    [(go!"etcdserverpb.KV", kmds.map (·.MethodName'), ksds.map (·.StreamName')),
     (go!"etcdserverpb.Watch", [], wsds.map (·.StreamName')),
     (go!"etcdserverpb.Lease", lmds.map (·.MethodName'), lsds.map (·.StreamName')),
     (go!"etcdserverpb.Cluster", cmds.map (·.MethodName'), csds.map (·.StreamName')),
     (go!"etcdserverpb.Auth", amds.map (·.MethodName'), asds.map (·.StreamName')),
     (go!"etcdserverpb.Maintenance", mmds.map (·.MethodName'), msds.map (·.StreamName'))]
  have hperm : ((regs ++ sregs).map Prod.fst).Perm (spikeNames S ++ (rs ++ srs).map Prod.fst) := by
    rw [List.perm_iff_count]
    intro a
    simp only [regs, sregs, S, spikeNames, List.flatMap_cons, List.flatMap_nil, List.map_append,
      spike_descRegs_names, spike_descSRegs_names, List.count_append, List.map_nil, List.append_nil,
      List.nil_append]
    omega
  refine (List.Perm.nodup_iff hperm).mpr (List.nodup_append.mpr ⟨?_, hH, ?_⟩)
  · apply spike_names_nodup
    · intro s hs
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
      · refine ⟨by dsimp only; decide, ?_⟩; rw [hk, hks]; decide
      · refine ⟨by dsimp only; decide, ?_⟩; rw [hws]; decide
      · refine ⟨by dsimp only; decide, ?_⟩; rw [hl, hls]; decide
      · exact ⟨by dsimp only; decide, hc⟩
      · exact ⟨by dsimp only; decide, by rw [has, List.append_nil]; exact ha⟩
      · exact ⟨by dsimp only; decide, hm⟩
    · simp only [S, List.map_cons, List.map_nil]; decide
  · intro a ha b hb hab
    subst hab
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
    obtain ⟨t, ht⟩ := hHp x hx
    obtain ⟨s, hs, hsa⟩ := List.mem_flatMap.mp ha
    obtain ⟨y, _, hy⟩ := List.mem_map.mp hsa
    have hfull : x.1 = grpcFullName go!"grpc.health.v1.Health" t := by
      rw [← ht, spike_health_prefix]; simp [grpcFullName, List.append_assoc]
    have hS1 : (47 : w8) ∉ s.1 ∧ s.1 ≠ go!"grpc.health.v1.Health" := by
      simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by dsimp only; decide, by dsimp only; decide⟩
    have := (spike_grpcFullName_inj s.1 go!"grpc.health.v1.Health" y t hS1.1 (by decide)
      (hy.trans hfull)).1
    exact hS1.2 this

end nodupEtcd

end EtcdGrove
end Perennial
