/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3alarm/AlarmStore__restore.lean`
(prove-ps2-v3alarm, 2026-11-24; until then a trust-boundary axiom): `restore`'s body over schema's alarm
backend, translated with its bodies (`CreateAlarmBucket`, `GetAllAlarms`, `ForceCommit`): the bucket
created (the part idle, one write-back), every alarm read (none: the idle-read law), no record added to
`a.types` (the loop over an empty slice), the commit (the second write-back). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__CreateAlarmBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__GetAllAlarms
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.alarmBackend__ForceCommit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.Assumptions]

theorem v3alarm.AlarmStore.restore.wp_proof
    (hCAB : schema.alarmBackend.CreateAlarmBucket.spec (GF := GF) (hG := hG))
    (hGAA : schema.alarmBackend.GetAllAlarms.spec (GF := GF) (hG := hG))
    (hFC : schema.alarmBackend.ForceCommit.spec (GF := GF) (hG := hG)) :
    v3alarm.AlarmStore.restore.spec (GF := GF) (hG := hG) := by
  intro a abl lg be dq γB P W Pk qo S r tm gm hS hRB hhas
  wp_start as ⟨Hbe, #Hbb, #Hbl, %Hlgnn, %Hablnn, Htypes, Hm, #HB, Ho, Hwb1, Hwb2, Hpl, Htk, Hrb, %Hr, Hct⟩
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  iunfold backend.bkRPool at Hpl
  icases Hpl with ⟨#Hrp, Hpo⟩
  wp_auto
  -- `a.be.CreateAlarmBucket()`: the bucket present and empty, the part idle
  wp_apply (hCAB abl γB P W Pk be qo S r hS hRB hhas) $$ [$Hspkg $Hbb $HB $Ho $Hwb1 $Hrb]
    as ⟨Ho, Hrb⟩
  rw [Hr]
  -- the alarm bucket's idle part apart from the rest
  have hsplit : ∀ n, S n ↔ (n = go!"alarm" ∨ (S n ∧ n ≠ go!"alarm")) := by
    intro n; by_cases hn : n = go!"alarm"
    · subst hn; exact ⟨fun _ => Or.inl rfl, fun _ => hS⟩
    · exact ⟨fun h => Or.inr ⟨h, hn⟩, fun h => h.elim (fun e => absurd e hn) And.left⟩
  ihave Hrb := (backend.rbOwnIn_set γB S _ _ hsplit).1 $$ Hrb
  icases (backend.rbOwnIn_split γB (· = go!"alarm") (fun n => S n ∧ n ≠ go!"alarm") _
    (fun n h1 h2 => h2.2 h1)).1 $$ Hrb with ⟨HrbA, HrbR⟩
  -- `a.be.GetAllAlarms()`: no record, no error
  wp_apply (hGAA abl γB P W Pk be qo (r.insert go!"alarm" ∅) hRB hhas
      (by rw [GMap.lookup_insert]; rfl)) $$ [$Hspkg $Hbb $HB $Ho $Hrp $Htk $HrbA $Hct]
    as %ms %err ⟨%Herr, Hms, Ho, Htk, HrbA, Hct⟩
  subst Herr
  ihave %Hlen := ownSlice_len ms _ _ $$ Hms
  (try wp_auto)
  -- the range over `ms`: empty
  ihave IH : i_ptr ↦ W64 0 $$ [i]
  · iexact i
  wp_for IH
  wp_if_destruct
  · exfalso
    simp only [List.length_nil] at Hlen
    word
  (try wp_auto)
  -- `a.be.ForceCommit()`: the value method on the loaded `*abl`
  ihave #Habl : abl ↦□ (go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.mk lg
      (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be)) $$ []
  · iapply typedPointsto_combine _ _ _ Hablnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe #
  wp_method_call
  (try wp_auto)
  wp_apply (hFC (go_etcd_io.etcd.server.v3.storage.schema.alarmBackend.mk lg
      (interface.mkOk
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #be)) γB P W Pk be qo rfl) $$ [$Hspkg $HB $Ho $Hwb2] as Ho
  (try wp_auto)
  ihave Hrb := (backend.rbOwnIn_split γB (· = go!"alarm") (fun n => S n ∧ n ≠ go!"alarm") _
    (fun n h1 h2 => h2.2 h1)).2 $$ [$HrbA $HrbR]
  ihave Hrb := (backend.rbOwnIn_set γB S _ _ hsplit).2 $$ Hrb
  iapply HΦ
  iframe Hbe Htypes Hm Ho Htk Hrb Hct
  isplitr
  · ipureintro; rfl
  iunfold backend.bkRPool
  iframe Hrp Hpo

end proof

end EtcdGrove
end Perennial
