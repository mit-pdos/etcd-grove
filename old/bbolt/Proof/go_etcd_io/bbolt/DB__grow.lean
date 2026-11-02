module
public import Spec.go_etcd_io.bbolt.DB__grow
public import Spec.go_etcd_io.bbolt.DB__Logger
public import Spec.go_etcd_io.bbolt.DB__growSize
public import Spec.os.File__Truncate
public import Spec.os.File__Sync
public import Proof.os.FileLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

variable [os_fi : OsFileInfoAssumptions (GF := GF)]
variable [linux : GOOSLinux]

theorem DB.grow.wp_proof (hLogger : DB.Logger.spec (GF := GF) (hG := hG))
    (hfileSize : DB.fileSize.spec (GF := GF) (hG := hG))
    (hErrorf : DefaultLogger.Errorf.spec (GF := GF) (hG := hG))
    (hgrowSize : DB.growSize.spec (GF := GF) (hG := hG))
    (hTruncate : os.File.Truncate.spec (GF := GF) (hG := hG))
    (hSync : os.File.Sync.spec (GF := GF) (hG := hG)) :
    DB.grow.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs m dq lg dl ps dsz al ngs ro sz Hdbl Hbl Hps Hsz Hdsz Hal Hszal Hdsz2 Hbd Hszd Hlg
  wp_start as ⟨Hlgf, Hf, Hp, Hdz, Hal', Hngs, Hro, Hml, #Hdl, #Hdlok, #Hfile, Hbytes, Hmap⟩
  wp_auto
  wp_apply hLogger dbl dq lg dl Hdbl $$ [Hlgf Hdl] as Hlgf
  · iframe; iexact Hdl
  have Hd : (if lg = interface.nil then discardIface dl else lg) = discardIface dl := by
    rcases Hlg with rfl | rfl <;> simp [discardIface, interface.mkOk]
  rw [Hd]
  try wp_auto
  wp_apply hfileSize dbl f fd bs ps dq dq Hbl Hps $$ [Hf Hp Hbytes] as %fs %err ⟨Hf, Hp, Hbytes, %Hfs⟩
  · iframe; iframe #
  try wp_auto
  ihave Hm0 : mapRange m bs bs.length bs.length $$ []
  · iapply (mapRange_empty m bs _ _ (Nat.le_refl _)).2; iempintro
  cases err with
  | ok ei =>
    -- `fileSize` failed: log it, return its error
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    try wp_auto
    wp_apply hErrorf dl _ _ $$ [Hdlok]
    · iframe; iexact Hdlok
    try wp_auto
    iapply HΦ
    iexists bs
    iframe
    ipureintro; exact ⟨Or.inl rfl, fun h => by cases h⟩
  | nil =>
    obtain ⟨Hfs1, Hfs2⟩ := Hfs.1 rfl
    subst Hfs1
    try wp_auto
    wp_if_destruct
    · -- big enough
      try wp_auto
      iapply HΦ
      iexists bs
      iframe
      ipureintro; exact ⟨Or.inl rfl, fun _ => Or.inl (by word)⟩
    try wp_auto
    wp_apply hgrowSize dbl al dq dsz sz $$ [Hal'] as Hal'
    · iframe
    try wp_auto
    rw [GOOSLinux.goos]
    try wp_auto
    cases ngs <;> cases ro
    · -- grow the file
      try wp_auto
      generalize Hn : (if sint.Z dsz ≤ sint.Z al then dsz else sz + al) = n
      have Hn0 : 0 ≤ sint.Z n := by rw [← Hn]; split <;> word
      have Hnb : bs.length ≤ sint.nat n := by rw [← Hn]; split <;> word
      ihave Hm1 : mapRange m bs (min (sint.nat n) bs.length) (max (sint.nat n) bs.length) $$ []
      · iapply (mapRange_beyond m bs _ _ (by omega)).2; iempintro
      have Hns : sint.Z sz ≤ sint.nat n := by rw [← Hn]; split <;> word
      wp_apply hTruncate f fd bs m n Hn0 $$ [Hbytes Hmap Hm1] as %e1 ⟨%bs', %Hbs', Hbytes, Hmap, Hm1⟩
      · iframe; iframe #
      rw [Nat.min_eq_right Hnb, Nat.max_eq_left Hnb] at *
      have Hbs2 : bs' = truncBytes bs (sint.nat n) ∨ bs' = bs := by
        rcases Hbs' with h | ⟨_, h⟩ <;> simp [h]
      ihave Hm1 := mapRange_grown m bs bs' _ Hnb Hbs2 $$ Hm1
      have Hpost : bs' = bs ∨ ∃ k, bs' = truncBytes bs k ∧ bs.length ≤ k := by
        rcases Hbs2 with h | h
        · exact Or.inr ⟨_, h, Hnb⟩
        · exact Or.inl h
      cases e1 with
      | ok ei =>
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl ⟨Hsl, -⟩
        try wp_auto
        wp_apply hErrorf dl _ _ $$ [Hdlok]
        · iframe; iexact Hdlok
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply fmt.wp_Errorf $$ [$Hsl2] as %e2 _
        try wp_auto
        iapply HΦ
        iexists bs'
        iframe
        ipureintro; exact ⟨Hpost, fun h => by cases h⟩
      | nil =>
        have Hbt : bs' = truncBytes bs (sint.nat n) := by
          rcases Hbs' with h | ⟨h, _⟩
          · exact h
          · exact absurd rfl h
        try wp_auto
        wp_apply hSync f as %e2 _
        try wp_auto
        cases e2 with
        | ok ei =>
          try wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl ⟨Hsl, -⟩
          try wp_auto
          wp_apply hErrorf dl _ _ $$ [Hdlok]
          · iframe; iexact Hdlok
          try wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %sl2 ⟨Hsl2, -⟩
          wp_apply fmt.wp_Errorf $$ [$Hsl2] as %e3 _
          try wp_auto
          iapply HΦ
          iexists bs'
          iframe
          ipureintro; exact ⟨Hpost, fun h => by cases h⟩
        | nil =>
          try wp_auto
          iapply HΦ
          iexists bs'
          iframe
          ipureintro
          refine ⟨Hpost, fun _ => Or.inl ?_⟩
          rw [Hbt, truncBytes_length bs _ Hnb]; omega
    all_goals
      try wp_auto
      iapply HΦ
      iexists bs
      iframe
      ipureintro; exact ⟨Or.inl rfl, fun _ => by simp⟩

end proof

end bbolt
end EtcdGrove
end Perennial
