/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/naiveExecuteCmd.lean`, run `rabia-r1wake-1`.)

`(*Proxy).naiveExecuteCmd`: a command of the workload (`"0"+key+value` or `"1"+key`, keys of
`KeyLen` bytes) on the in-memory store: the model's `execCmd`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.Basics
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.proxy

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia.roles.server.layers.consensus rabia

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.proxy.Assumptions]

theorem Proxy.wp_naiveExecuteCmd (cf : RCfg) (p : Loc) (kv : GoMap) (m : GMap GoString GoString) (s : KStore)
    (cmd : GoString) (hlen : 1 + keyLen ≤ cmd.length) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy ∗ confRO cf ∗
      structFieldRef Proxy go!"KVStore" p ↦□ kv ∗ ownMap kv (DFrac.own 1) m ∗ ⌜StoreRel m s⌝ }}
    (App (Val (p @!! go.GoType.PointerType Proxy.ty @!! go!"naiveExecuteCmd")) (Val #cmd))
  {{ (m' : GMap GoString GoString), RET #((execCmd s cmd).2);
      ownMap kv (DFrac.own 1) m' ∗ ⌜StoreRel m' (execCmd s cmd).1⌝ }} := by
  wp_start as ⟨#Hconf, #HKV, Hm, %Hrel⟩
  icases confRO_val $$ Hconf with ⟨%ps, #Hc⟩
  iStructNamed Hc
  have hk : keyLen = 8 := rfl
  have hl : (9 : Int) ≤ (cmd.length : Int) := by omega
  wp_auto
  rw [ite_eq_left (by word)]
  wp_auto
  simp only [confVal]
  rw [ite_eq_left (by word)]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hslen
  rw [ite_eq_left (by word)]
  wp_auto
  have h9 : sint.nat (W64 1 + W64 8) = 1 + keyLen := rfl
  simp only [h9, Nat.add_sub_cancel_left, Nat.sub_zero, List.drop_zero]
  wp_if_destruct
  · wp_apply wp_mapInsert $$ [$Hm] as Hm
    have ht : cmd.take 1 = [48#8] := Hif
    have e : execCmd s cmd = ((fun k => if k = (cmd.drop 1).take keyLen then
        some (cmd.drop (1 + keyLen)) else s k), (48#8) :: (cmd.drop 1).take keyLen ++ [111#8, 107#8]) := by
      simp only [execCmd, ht, ↓reduceIte]
    rw [e]
    simp only [List.cons_append, List.nil_append]
    iapply HΦ
    iframe Hm
    ipureintro
    have hv : List.take (sint.nat (W64 ↑(cmd.length)) - (1 + keyLen)) (List.drop (1 + keyLen) cmd) =
        List.drop (1 + keyLen) cmd := by
      apply List.take_of_length_le
      simp only [List.length_drop]
      have : sint.nat (W64 ↑(cmd.length)) = cmd.length := by word
      omega
    rw [hv]
    exact storeRel_put Hrel _ _
  · wp_apply wp_map_lookup1 $$ [$Hm] as Hm
    have ht : ¬ cmd.take 1 = [48#8] := Hif
    have e : execCmd s cmd = (s, (49#8) :: (cmd.drop 1).take keyLen ++
        (s ((cmd.drop 1).take keyLen)).getD []) := by
      simp only [execCmd, ht, ↓reduceIte]
    rw [e, ← Hrel, show (Perennial.zero_val GoString) = [] from rfl]
    simp only [List.cons_append, List.nil_append]
    iapply HΦ
    iframe Hm
    ipureintro
    exact Hrel

end proof
end Perennial.rabia.roles.server.layers.proxy
