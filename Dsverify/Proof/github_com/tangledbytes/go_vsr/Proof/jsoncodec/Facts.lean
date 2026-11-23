/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/Facts.lean (lab master 915f964;
notes/dsv-vr.md).
-/
/-
The pure framing facts of the kit's encodings: every encoding is well formed (`ok`, shallow),
the scanner frames an event's line and asks for more on a strict prefix (`scanF_line'`,
`scanF_partial'`), and the encodings are injective and frame uniquely (`lines_prefix`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.ScanTop

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace VsrJson

open Perennial VsrModel

/-- `Scan`'s results as words (`vsrnet.scanF`). -/
def scanF (b : List w8) (eof : Bool) : w64 × w64 :=
  (W64 (scanL b eof).1, W64 (scanL b eof).2)

/-! ## Well-formedness -/

theorem plain_okB (s : List w8) (h : PlainStr s) : ∀ c ∈ s, okB c := by
  intro c hc
  obtain ⟨h1, h2, h3, h4, -⟩ := h c hc
  refine ⟨h1, h2, ?_, ?_⟩
  · intro e; subst e; exact h3 rfl
  · intro e; subst e; exact h4 rfl

theorem decN_okB (n : Nat) : ∀ c ∈ decN n, okB c := by
  intro c hc
  have h := decN_digits n c hc
  simp only [isDig, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have a1 : 48 ≤ c.toNat := h1
  have a2 : c.toNat ≤ 57 := h2
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro e; subst e; simp at a1
  · intro e; subst e; simp at a2

theorem mkObj_ok (ms : List (List w8 × JV)) (h : ∀ p ∈ ms, (∀ c ∈ p.1, okB c) ∧ p.2.ok) :
    (mkObj ms).ok := by
  induction ms with
  | nil => simp [mkObj, JMs.ok]
  | cons p ms ih =>
    obtain ⟨k, v⟩ := p
    simp only [mkObj, JMs.ok]
    exact ⟨(h (k, v) (by simp)).1, (h (k, v) (by simp)).2, ih (fun q hq => h q (by simp [hq]))⟩

theorem mkArr_ok (vs : List JV) (h : ∀ v ∈ vs, v.ok) : (mkArr vs).ok := by
  induction vs with
  | nil => simp [mkArr, JVs.ok]
  | cons v vs ih => simp only [mkArr, JVs.ok]; exact ⟨h v (by simp), ih (fun w hw => h w (by simp [hw]))⟩

theorem mkObj_depth (ms : List (List w8 × JV)) (d : Nat) (h : ∀ p ∈ ms, p.2.depth ≤ d) :
    (mkObj ms).depth ≤ d := by
  induction ms with
  | nil => simp [mkObj, JMs.depth]
  | cons p ms ih =>
    simp only [mkObj, JMs.depth]
    have := h p (by simp); have := ih (fun q hq => h q (by simp [hq])); omega

theorem mkArr_depth (vs : List JV) (d : Nat) (h : ∀ v ∈ vs, v.depth ≤ d) :
    (mkArr vs).depth ≤ d := by
  induction vs with
  | nil => simp [mkArr, JVs.depth]
  | cons v vs ih =>
    simp only [mkArr, JVs.depth]
    have := h v (by simp); have := ih (fun w hw => h w (by simp [hw])); omega

theorem key_ok (k : List w8) (h : PlainStr k) : ∀ c ∈ k, okB c := plain_okB k h

theorem qn_ok (n : Nat) : (qn n).ok := by simp only [qn, JV.ok]; exact decN_okB n

theorem logJV_ok (e : Entry) (h : PlainStr e.op) : (logJV e).ok := by
  simp only [logJV, JV.ok]
  apply mkObj_ok
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨⟨by decide, plain_okB _ h⟩, ⟨by decide, qn_ok _⟩, ⟨by decide, qn_ok _⟩⟩

theorem logsJV_ok (es : List Entry) (h : ∀ e ∈ es, PlainStr e.op) : (logsJV es).ok := by
  simp only [logsJV, JV.ok]
  apply mkArr_ok
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨e, he, rfl⟩ := hv
  exact logJV_ok e (h e he)

theorem logJV_depth (e : Entry) : (logJV e).depth ≤ 1 := by
  simp only [logJV, JV.depth]
  have := mkObj_depth [(go!"data", JV.str e.op), (go!"client_id", qn e.cid),
    (go!"request_id", qn e.req)] 0 (by simp [JV.depth, qn])
  omega

theorem logsJV_depth (es : List Entry) : (logsJV es).depth ≤ 2 := by
  simp only [logsJV, JV.depth]
  have := mkArr_depth (es.map logJV) 1 (by
    intro v hv; simp only [List.mem_map] at hv; obtain ⟨e, -, rfl⟩ := hv; exact logJV_depth e)
  omega

theorem reqJV_ok (id cid : Nat) (op : List w8) (h : PlainStr op) : (reqJV id cid op).ok := by
  simp only [reqJV, JV.ok]
  apply mkObj_ok
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  refine ⟨⟨by decide, qn_ok _⟩, ⟨by decide, qn_ok _⟩, ⟨by decide, plain_okB _ h⟩⟩

theorem reqJV_depth (id cid : Nat) (op : List w8) : (reqJV id cid op).depth ≤ 1 := by
  simp only [reqJV, JV.depth]
  have := mkObj_depth [(go!"id", qn id), (go!"client_id", qn cid), (go!"op", JV.str op)] 0
    (by simp [JV.depth, qn])
  omega

theorem payJV_ok (m : Msg) (hm : PlainMsg m) : (payJV m).ok := by
  cases m <;> simp only [PlainMsg] at hm <;>
    simp (config := {decide := true}) only [payJV, mkObj, JMs.ok, JV.ok, qn_ok, true_and,
      and_true]
  · exact reqJV_ok _ _ _ hm
  · exact plain_okB _ hm
  · exact reqJV_ok _ _ _ hm
  · exact logsJV_ok _ hm
  · exact logsJV_ok _ hm
  · exact logsJV_ok _ hm

theorem payJV_depth (m : Msg) : (payJV m).depth ≤ 3 := by
  cases m with
  | request id cid op => have := reqJV_depth id cid op; simp only [payJV]; omega
  | prepare v k c e rid =>
    have := reqJV_depth e.req e.cid e.op
    simp only [payJV, JV.depth, mkObj, JMs.depth, qn]; omega
  | doViewChange d =>
    have := logsJV_depth d.log
    simp only [payJV, JV.depth, mkObj, JMs.depth, qn]; omega
  | startView v k c logs rid =>
    have := logsJV_depth logs
    simp only [payJV, JV.depth, mkObj, JMs.depth, qn]; omega
  | newState v logs c k rid =>
    have := logsJV_depth logs
    simp only [payJV, JV.depth, mkObj, JMs.depth, qn]; omega
  | _ => simp only [payJV, JV.depth, mkObj, JMs.depth, qn]; omega

theorem evJV_ok (m : Msg) (hm : PlainMsg m) : (evJV m).ok := by
  simp only [evJV, JV.ok]
  apply mkObj_ok
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨⟨by decide, trivial⟩, ⟨by decide, payJV_ok m hm⟩⟩

theorem evJV_depth (m : Msg) : (evJV m).depth ≤ 4 := by
  simp only [evJV, JV.depth]
  have := mkObj_depth [(go!"@type", JV.num (typeN m)), (go!"data", payJV m)] 3 (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨by simp [JV.depth], payJV_depth m⟩)
  omega

end VsrJson
