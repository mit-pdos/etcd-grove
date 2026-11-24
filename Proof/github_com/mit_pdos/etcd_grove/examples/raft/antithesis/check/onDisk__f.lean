/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.f()` (B 291-359, `OnDisk.f`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__f
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__leads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__es
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__stores
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__moved
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermAt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem onDisk.f.wp_proof
    (wp_leads : onDisk.leads.spec (GF := GF) (hG := hG))
    (wp_T1 : onDisk.T1.spec (GF := GF) (hG := hG))
    (wp_es : onDisk.es.spec (GF := GF) (hG := hG))
    (wp_stores : onDisk.stores.spec (GF := GF) (hG := hG))
    (wp_first : onDisk.first.spec (GF := GF) (hG := hG))
    (wp_moved : onDisk.moved.spec (GF := GF) (hG := hG))
    (wp_fm : onDisk.fm.spec (GF := GF) (hG := hG))
    (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_commit : Event.commit.spec (GF := GF) (hG := hG))
    (wp_Has : TermLogs.Has.spec (GF := GF) (hG := hG))
    (wp_Get : TermLogs.Get.spec (GF := GF) (hG := hG))
    (wp_TermAt : TermAt.spec (GF := GF) (hG := hG)) :
    onDisk.f.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold onDiskRO at Hx'
  icases Hx' with ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hp⟩
  obtain ⟨Hn, Hlt, Hmore, Hrol, HB⟩ := Hp
  have Hn0 : 0 ≤ sint.Z gx.n' := by omega
  have hnn : sint.nat gx.n' = x.n := by have := sint_nat_cast Hn0; omega
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hgc, #Hsrv, #-, %-⟩
  iStructNamed Hgc
  obtain ⟨b, E, hb, HW⟩ := HB.get
  unfold OnDisk.f at Hv
  obtain ⟨ld, hld, Hv⟩ := bind_ok Hv
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'leads.method_unfold]
  try wp_auto
  wp_apply wp_leads gx x ld $$ [Hx]
  · iframe Hx; ipureintro; exact hld
  try wp_auto
  cases ld
  · simp only [Bool.false_eq_true, ite_false] at Hv
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'fm.method_unfold]
    try wp_auto
    wp_apply wp_fm gx x v $$ [Hx] as %u #Hu
    · iframe Hx; ipureintro; exact Hv
    try wp_auto
    iapply HΦ; iexact Hu
  simp only [ite_true] at Hv
  obtain ⟨t1, ht1, Hv⟩ := bind_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'T1.method_unfold]
  try wp_auto
  wp_apply wp_T1 gx x t1 $$ [Hx] as %ut %Hut
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  ihave #Hme := strsRO_at gc.Server' x.s.cfg.server gx.n' ⟨Hn0, by omega⟩ $$ Hsrv
  wp_apply wp_load_at _ _ _ Hn0 $$ [Hme] as -
  · iexact Hme
  try wp_auto
  wp_apply wp_load_at _ _ _ Hn0 $$ [Hme] as -
  · iexact Hme
  try wp_auto
  obtain ⟨es, hes, Hv⟩ := bind_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'es.method_unfold]
  try wp_auto
  wp_apply wp_es gx x es $$ [Hx] as %esl #Hes
  · iframe Hx; ipureintro; exact hes
  try wp_auto
  try dsimp only at Hv
  obtain ⟨st, hst, Hv⟩ := bind_ok Hv
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'stores.method_unfold]
  try wp_auto
  wp_apply wp_stores gx x st $$ [Hx]
  · iframe Hx; ipureintro; exact hst
  try wp_auto
  cases st
  · have hfirst : True := trivial
    -- not storing: `PrevLogIndex` and `PrevLogTerm` stay 0
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'stores.method_unfold]
    try wp_auto
    wp_apply wp_stores gx x false $$ [Hx]
    · iframe Hx; ipureintro; exact hst
    try wp_auto
    have hh : (x.ll.has t1 && false) = false := by simp
    cases hm' : x.moved with
    | error e => simp [hst,   hh, hm', andM] at Hv
    | ok mv =>
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'moved.method_unfold]
    try wp_auto
    wp_apply wp_moved gx x mv $$ [Hx]
    · iframe Hx; ipureintro; exact hm'
    try wp_auto
    cases mv
    · have hv : v = { src := x.s.cfg.server[x.n]!, dst := x.s.cfg.server[x.n]!, term := t1, prevLogIndex := 0, prevLogTerm := 0, entries := es, commit := 0 } := by
        simp [hst,   hh, hm', andM] at Hv; rw [← Hv]; simp
      try wp_auto
      iapply HΦ
      iunfold appendFactRO
      rw [hv, ← hnn]
      iframe Hes
      ipureintro
      exact ⟨rfl, rfl, Hut, rfl, rfl, rfl⟩
    · cases hc : need x.w.commit with
      | error e => simp [hst,   hh, hm', hc, andM] at Hv
      | ok c =>
      have hv : v = { src := x.s.cfg.server[x.n]!, dst := x.s.cfg.server[x.n]!, term := t1, prevLogIndex := 0, prevLogTerm := 0, entries := es, commit := c } := by
        simp [hst,   hh, hm', hc, andM] at Hv; rw [← Hv]; simp
      try wp_auto
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
      try wp_auto
      wp_apply wp_w gx x  $$ [Hx] as %e #He
      · iexact Hx
      try wp_auto
      wp_apply wp_commit e x.w c $$ [He] as %uc %Huc
      · iframe He; ipureintro; exact hc
      try wp_auto
      iapply HΦ
      iunfold appendFactRO
      rw [hv, ← hnn]
      iframe Hes
      ipureintro
      exact ⟨rfl, rfl, Hut, rfl, rfl, Huc⟩
  · cases hfirst : x.first with
    | error e => simp [hfirst] at Hv
    | ok fi =>
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'first.method_unfold]
    try wp_auto
    wp_apply wp_first gx x fi $$ [Hx] as %ufi %Hufi
    · iframe Hx; ipureintro; exact hfirst
    try wp_auto
    have hfb := OnDisk.first_bounds hb HW hfirst
    have Hfi : sint.Z (ufi - W64 1) = fi - 1 := by
      rw [sint_sub (by rw [Hufi, sint_one]; unfold numBound at hb; omega) (by rw [Hufi, sint_one]; omega), Hufi, sint_one]
    try wp_auto
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'stores.method_unfold]
    try wp_auto
    wp_apply wp_stores gx x true $$ [Hx]
    · iframe Hx; ipureintro; exact hst
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_unfold'Has.method_unfold]
    try wp_auto
    wp_apply wp_Has gx.ll' x.ll ut $$ [Hll]
    · iexact Hll
    rw [Hut]
    cases hh : x.ll.has t1
    · try wp_auto
      cases hm' : x.moved with
      | error e => simp [hst, hfirst,  hh, hm', andM] at Hv
      | ok mv =>
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'moved.method_unfold]
      try wp_auto
      wp_apply wp_moved gx x mv $$ [Hx]
      · iframe Hx; ipureintro; exact hm'
      try wp_auto
      cases mv
      · have hv : v = { src := x.s.cfg.server[x.n]!, dst := x.s.cfg.server[x.n]!, term := t1, prevLogIndex := fi - 1, prevLogTerm := 0, entries := es, commit := 0 } := by
          simp [hst, hfirst,  hh, hm', andM] at Hv; rw [← Hv]; simp
        try wp_auto
        iapply HΦ
        iunfold appendFactRO
        rw [hv, ← hnn]
        iframe Hes
        ipureintro
        exact ⟨rfl, rfl, Hut, Hfi, rfl, rfl⟩
      · cases hc : need x.w.commit with
        | error e => simp [hst, hfirst,  hh, hm', hc, andM] at Hv
        | ok c =>
        have hv : v = { src := x.s.cfg.server[x.n]!, dst := x.s.cfg.server[x.n]!, term := t1, prevLogIndex := fi - 1, prevLogTerm := 0, entries := es, commit := c } := by
          simp [hst, hfirst,  hh, hm', hc, andM] at Hv; rw [← Hv]; simp
        try wp_auto
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
        try wp_auto
        wp_apply wp_w gx x  $$ [Hx] as %e #He
        · iexact Hx
        try wp_auto
        wp_apply wp_commit e x.w c $$ [He] as %uc %Huc
        · iframe He; ipureintro; exact hc
        try wp_auto
        iapply HΦ
        iunfold appendFactRO
        rw [hv, ← hnn]
        iframe Hes
        ipureintro
        exact ⟨rfl, rfl, Hut, Hfi, rfl, Huc⟩
    · cases hg : x.ll.get t1 with
      | error e => simp [hst, hfirst, hg, hh, andM] at Hv
      | ok l =>
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermLogs.TypeAssumptions.ptr_unfold'Get.method_unfold]
      try wp_auto
      wp_apply wp_Get gx.ll' x.ll ut l $$ [Hll] as %lsl #Hl
      · iframe Hll; ipureintro; rw [Hut]; exact hg
      try wp_auto
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'first.method_unfold]
      try wp_auto
      wp_apply wp_first gx x fi $$ [Hx] as %ufi2 %Hufi2
      · iframe Hx; ipureintro; exact hfirst
      try wp_auto
      have Hfi2 : sint.Z (ufi2 - W64 1) = fi - 1 := by
        rw [sint_sub (by rw [Hufi2, sint_one]; unfold numBound at hb; omega) (by rw [Hufi2, sint_one]; omega), Hufi2, sint_one]
      wp_apply wp_TermAt lsl l (ufi2 - W64 1) $$ [Hl] as %r %Hr
      · iexact Hl
      rw [Hfi2] at Hr
      try wp_auto
      cases hm' : x.moved with
      | error e => simp [hst, hfirst, hg, hh, hm', andM] at Hv
      | ok mv =>
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'moved.method_unfold]
      try wp_auto
      wp_apply wp_moved gx x mv $$ [Hx]
      · iframe Hx; ipureintro; exact hm'
      try wp_auto
      cases mv
      · have hv : v = { src := x.s.cfg.server[x.n]!, dst := x.s.cfg.server[x.n]!, term := t1, prevLogIndex := fi - 1, prevLogTerm := termAt l (fi - 1), entries := es, commit := 0 } := by
          simp [hst, hfirst, hg, hh, hm', andM] at Hv; rw [← Hv]; simp
        try wp_auto
        iapply HΦ
        iunfold appendFactRO
        rw [hv, ← hnn]
        iframe Hes
        ipureintro
        exact ⟨rfl, rfl, Hut, Hfi, Hr, rfl⟩
      · cases hc : need x.w.commit with
        | error e => simp [hst, hfirst, hg, hh, hm', hc, andM] at Hv
        | ok c =>
        have hv : v = { src := x.s.cfg.server[x.n]!, dst := x.s.cfg.server[x.n]!, term := t1, prevLogIndex := fi - 1, prevLogTerm := termAt l (fi - 1), entries := es, commit := c } := by
          simp [hst, hfirst, hg, hh, hm', hc, andM] at Hv; rw [← Hv]; simp
        try wp_auto
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
        try wp_auto
        wp_apply wp_w gx x  $$ [Hx] as %e #He
        · iexact Hx
        try wp_auto
        wp_apply wp_commit e x.w c $$ [He] as %uc %Huc
        · iframe He; ipureintro; exact hc
        try wp_auto
        iapply HΦ
        iunfold appendFactRO
        rw [hv, ← hnn]
        iframe Hes
        ipureintro
        exact ⟨rfl, rfl, Hut, Hfi, Hr, Huc⟩

end proof

end AntCheck
end EtcdGrove
end Perennial
