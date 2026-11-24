/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.acks()` (B 291-359, `OnDisk.acks`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__acks
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__stores
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__leads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__moved
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__hasM
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__m
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__typ
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__takes
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__below
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

theorem onDisk.acks.wp_proof
    (wp_stores : onDisk.stores.spec (GF := GF) (hG := hG))
    (wp_leads : onDisk.leads.spec (GF := GF) (hG := hG))
    (wp_moved : onDisk.moved.spec (GF := GF) (hG := hG))
    (wp_hasM : onDisk.hasM.spec (GF := GF) (hG := hG))
    (wp_m : onDisk.m.spec (GF := GF) (hG := hG))
    (wp_typ : Msg.typ.spec (GF := GF) (hG := hG))
    (wp_takes : onDisk.takes.spec (GF := GF) (hG := hG))
    (wp_below : onDisk.below.spec (GF := GF) (hG := hG)) :
    onDisk.acks.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  unfold OnDisk.acks at Hv
  obtain ⟨av, hA, hA1, hA2⟩ := orM_ok Hv
  obtain ⟨st, hst, hAs1, hAs2⟩ := andM_ok hA
  wp_auto
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_stores_unfold.method_unfold]
  try wp_auto
  wp_apply wp_stores gx x st $$ [Hx]
  · iframe Hx; ipureintro; exact hst
  try wp_auto
  cases st
  · have := hAs2 rfl; subst this
    have HBC := hA2 rfl
    try wp_auto
    -- `x.moved() && !x.leads() && x.hasM() && (x.m().typ() == "app" || x.m().typ() == "snap")`
    obtain ⟨bv, hB, hB1, hB2⟩ := orM_ok HBC
    obtain ⟨mv, hmv, hBm1, hBm2⟩ := andM_ok hB
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_moved_unfold.method_unfold]
    try wp_auto
    wp_apply wp_moved gx x mv $$ [Hx]
    · iframe Hx; ipureintro; exact hmv
    try wp_auto
    cases mv
    · have := hBm2 rfl; subst this
      have HC := hB2 rfl
      try wp_auto
      -- `x.takes() || x.below()`
      obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
      try wp_auto
      wp_apply wp_takes gx x tk $$ [Hx]
      · iframe Hx; ipureintro; exact htk
      try wp_auto
      cases tk
      · have hbl := hC2 rfl
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
        try wp_auto
        wp_apply wp_below gx x v $$ [Hx]
        · iframe Hx; ipureintro; exact hbl
        try wp_auto
        iapply HΦ; ipureintro; trivial
      · rw [hC1 rfl]
        try wp_auto
        iapply HΦ; ipureintro; trivial
    · have hB' := hBm1 rfl
      obtain ⟨nl, hnl, hBn1, hBn2⟩ := andM_ok hB'
      unfold notM at hnl
      obtain ⟨l2, hl2, hnl⟩ := bind_ok hnl
      simp only [pure_ok, Except.ok.injEq] at hnl
      subst hnl
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_leads_unfold.method_unfold]
      try wp_auto
      wp_apply wp_leads gx x l2 $$ [Hx]
      · iframe Hx; ipureintro; exact hl2
      try wp_auto
      cases l2
      · have hB'' := hBn1 rfl
        obtain ⟨hm, hhm, hBh1, hBh2⟩ := andM_ok hB''
        simp only [pure_ok, Except.ok.injEq] at hhm
        subst hhm
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_hasM_unfold.method_unfold]
        try wp_auto
        wp_apply wp_hasM gx x  $$ [Hx]
        · iexact Hx
        try wp_auto
        cases hhm : x.hasM
        · have := hBh2 hhm; subst this
          have HC := hB2 rfl
          try wp_auto
          -- `x.takes() || x.below()`
          obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
          try wp_auto
          wp_apply wp_takes gx x tk $$ [Hx]
          · iframe Hx; ipureintro; exact htk
          try wp_auto
          cases tk
          · have hbl := hC2 rfl
            try wp_auto
            rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
            try wp_auto
            wp_apply wp_below gx x v $$ [Hx]
            · iframe Hx; ipureintro; exact hbl
            try wp_auto
            iapply HΦ; ipureintro; trivial
          · rw [hC1 rfl]
            try wp_auto
            iapply HΦ; ipureintro; trivial
        · have hB3 := hBh1 hhm
          obtain ⟨ta, hta, hBt1, hBt2⟩ := orM_ok hB3
          obtain ⟨m, hm, hta⟩ := bind_ok hta
          obtain ⟨ty, hty, hta⟩ := bind_ok hta
          simp only [pure_ok, Except.ok.injEq] at hta
          subst hta
          try wp_auto
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_m_unfold.method_unfold]
          try wp_auto
          wp_apply wp_m gx x m $$ [Hx] as %u #Hu
          · iframe Hx; ipureintro; exact hm
          try wp_auto
          wp_apply wp_typ u m ty $$ [Hu]
          · iframe Hu; ipureintro; exact hty
          try wp_auto
          by_cases happ : ty = go!"app"
          · rw [decide_eq_true happ]
            have := hBt1 (by simp [happ]); subst this
            rw [hB1 rfl]
            try wp_auto
            iapply HΦ; ipureintro; trivial
          · rw [decide_eq_false happ]
            have hB4 := hBt2 (by simp [happ])
            obtain ⟨m', hm', hB4⟩ := bind_ok hB4
            rw [hm] at hm'; cases hm'
            obtain ⟨ty', hty', hB4⟩ := bind_ok hB4
            rw [hty] at hty'; cases hty'
            simp only [pure_ok, Except.ok.injEq] at hB4
            try wp_auto
            try wp_auto
            rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_m_unfold.method_unfold]
            try wp_auto
            wp_apply wp_m gx x m $$ [Hx] as %u' #Hu'
            · iframe Hx; ipureintro; exact hm
            try wp_auto
            wp_apply wp_typ u' m ty $$ [Hu']
            · iframe Hu'; ipureintro; exact hty
            try wp_auto
            by_cases hsn : ty = go!"snap"
            · rw [decide_eq_true hsn]
              have : bv = true := by rw [← hB4]; simp [hsn]
              rw [hB1 this]
              try wp_auto
              iapply HΦ; ipureintro; trivial
            · rw [decide_eq_false hsn]
              have : bv = false := by rw [← hB4]; simp [hsn]
              have HC := hB2 this
              try wp_auto
              -- `x.takes() || x.below()`
              obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
              try wp_auto
              rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
              try wp_auto
              wp_apply wp_takes gx x tk $$ [Hx]
              · iframe Hx; ipureintro; exact htk
              try wp_auto
              cases tk
              · have hbl := hC2 rfl
                try wp_auto
                rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
                try wp_auto
                wp_apply wp_below gx x v $$ [Hx]
                · iframe Hx; ipureintro; exact hbl
                try wp_auto
                iapply HΦ; ipureintro; trivial
              · rw [hC1 rfl]
                try wp_auto
                iapply HΦ; ipureintro; trivial
      · have := hBn2 rfl; subst this
        have HC := hB2 rfl
        try wp_auto
        -- `x.takes() || x.below()`
        obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
        try wp_auto
        wp_apply wp_takes gx x tk $$ [Hx]
        · iframe Hx; ipureintro; exact htk
        try wp_auto
        cases tk
        · have hbl := hC2 rfl
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
          try wp_auto
          wp_apply wp_below gx x v $$ [Hx]
          · iframe Hx; ipureintro; exact hbl
          try wp_auto
          iapply HΦ; ipureintro; trivial
        · rw [hC1 rfl]
          try wp_auto
          iapply HΦ; ipureintro; trivial
  · have hAl := hAs1 rfl
    try wp_auto
    rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_leads_unfold.method_unfold]
    try wp_auto
    wp_apply wp_leads gx x av $$ [Hx]
    · iframe Hx; ipureintro; exact hAl
    try wp_auto
    cases av
    · have HBC := hA2 rfl
      try wp_auto
      -- `x.moved() && !x.leads() && x.hasM() && (x.m().typ() == "app" || x.m().typ() == "snap")`
      obtain ⟨bv, hB, hB1, hB2⟩ := orM_ok HBC
      obtain ⟨mv, hmv, hBm1, hBm2⟩ := andM_ok hB
      try wp_auto
      rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_moved_unfold.method_unfold]
      try wp_auto
      wp_apply wp_moved gx x mv $$ [Hx]
      · iframe Hx; ipureintro; exact hmv
      try wp_auto
      cases mv
      · have := hBm2 rfl; subst this
        have HC := hB2 rfl
        try wp_auto
        -- `x.takes() || x.below()`
        obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
        try wp_auto
        wp_apply wp_takes gx x tk $$ [Hx]
        · iframe Hx; ipureintro; exact htk
        try wp_auto
        cases tk
        · have hbl := hC2 rfl
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
          try wp_auto
          wp_apply wp_below gx x v $$ [Hx]
          · iframe Hx; ipureintro; exact hbl
          try wp_auto
          iapply HΦ; ipureintro; trivial
        · rw [hC1 rfl]
          try wp_auto
          iapply HΦ; ipureintro; trivial
      · have hB' := hBm1 rfl
        obtain ⟨nl, hnl, hBn1, hBn2⟩ := andM_ok hB'
        unfold notM at hnl
        obtain ⟨l2, hl2, hnl⟩ := bind_ok hnl
        simp only [pure_ok, Except.ok.injEq] at hnl
        subst hnl
        try wp_auto
        rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_leads_unfold.method_unfold]
        try wp_auto
        wp_apply wp_leads gx x l2 $$ [Hx]
        · iframe Hx; ipureintro; exact hl2
        try wp_auto
        cases l2
        · have hB'' := hBn1 rfl
          obtain ⟨hm, hhm, hBh1, hBh2⟩ := andM_ok hB''
          simp only [pure_ok, Except.ok.injEq] at hhm
          subst hhm
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_hasM_unfold.method_unfold]
          try wp_auto
          wp_apply wp_hasM gx x  $$ [Hx]
          · iexact Hx
          try wp_auto
          cases hhm : x.hasM
          · have := hBh2 hhm; subst this
            have HC := hB2 rfl
            try wp_auto
            -- `x.takes() || x.below()`
            obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
            try wp_auto
            rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
            try wp_auto
            wp_apply wp_takes gx x tk $$ [Hx]
            · iframe Hx; ipureintro; exact htk
            try wp_auto
            cases tk
            · have hbl := hC2 rfl
              try wp_auto
              rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
              try wp_auto
              wp_apply wp_below gx x v $$ [Hx]
              · iframe Hx; ipureintro; exact hbl
              try wp_auto
              iapply HΦ; ipureintro; trivial
            · rw [hC1 rfl]
              try wp_auto
              iapply HΦ; ipureintro; trivial
          · have hB3 := hBh1 hhm
            obtain ⟨ta, hta, hBt1, hBt2⟩ := orM_ok hB3
            obtain ⟨m, hm, hta⟩ := bind_ok hta
            obtain ⟨ty, hty, hta⟩ := bind_ok hta
            simp only [pure_ok, Except.ok.injEq] at hta
            subst hta
            try wp_auto
            try wp_auto
            rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_m_unfold.method_unfold]
            try wp_auto
            wp_apply wp_m gx x m $$ [Hx] as %u #Hu
            · iframe Hx; ipureintro; exact hm
            try wp_auto
            wp_apply wp_typ u m ty $$ [Hu]
            · iframe Hu; ipureintro; exact hty
            try wp_auto
            by_cases happ : ty = go!"app"
            · rw [decide_eq_true happ]
              have := hBt1 (by simp [happ]); subst this
              rw [hB1 rfl]
              try wp_auto
              iapply HΦ; ipureintro; trivial
            · rw [decide_eq_false happ]
              have hB4 := hBt2 (by simp [happ])
              obtain ⟨m', hm', hB4⟩ := bind_ok hB4
              rw [hm] at hm'; cases hm'
              obtain ⟨ty', hty', hB4⟩ := bind_ok hB4
              rw [hty] at hty'; cases hty'
              simp only [pure_ok, Except.ok.injEq] at hB4
              try wp_auto
              try wp_auto
              rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_m_unfold.method_unfold]
              try wp_auto
              wp_apply wp_m gx x m $$ [Hx] as %u' #Hu'
              · iframe Hx; ipureintro; exact hm
              try wp_auto
              wp_apply wp_typ u' m ty $$ [Hu']
              · iframe Hu'; ipureintro; exact hty
              try wp_auto
              by_cases hsn : ty = go!"snap"
              · rw [decide_eq_true hsn]
                have : bv = true := by rw [← hB4]; simp [hsn]
                rw [hB1 this]
                try wp_auto
                iapply HΦ; ipureintro; trivial
              · rw [decide_eq_false hsn]
                have : bv = false := by rw [← hB4]; simp [hsn]
                have HC := hB2 this
                try wp_auto
                -- `x.takes() || x.below()`
                obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
                try wp_auto
                rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
                try wp_auto
                wp_apply wp_takes gx x tk $$ [Hx]
                · iframe Hx; ipureintro; exact htk
                try wp_auto
                cases tk
                · have hbl := hC2 rfl
                  try wp_auto
                  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
                  try wp_auto
                  wp_apply wp_below gx x v $$ [Hx]
                  · iframe Hx; ipureintro; exact hbl
                  try wp_auto
                  iapply HΦ; ipureintro; trivial
                · rw [hC1 rfl]
                  try wp_auto
                  iapply HΦ; ipureintro; trivial
        · have := hBn2 rfl; subst this
          have HC := hB2 rfl
          try wp_auto
          -- `x.takes() || x.below()`
          obtain ⟨tk, htk, hC1, hC2⟩ := orM_ok HC
          try wp_auto
          rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_takes_unfold.method_unfold]
          try wp_auto
          wp_apply wp_takes gx x tk $$ [Hx]
          · iframe Hx; ipureintro; exact htk
          try wp_auto
          cases tk
          · have hbl := hC2 rfl
            try wp_auto
            rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_below_unfold.method_unfold]
            try wp_auto
            wp_apply wp_below gx x v $$ [Hx]
            · iframe Hx; ipureintro; exact hbl
            try wp_auto
            iapply HΦ; ipureintro; trivial
          · rw [hC1 rfl]
            try wp_auto
            iapply HΦ; ipureintro; trivial
    · rw [hA1 rfl]
      try wp_auto
      iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
