/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the package facts of its machines' first initialization

The tables of a machine's boot (as the dsverify kits', `etc/dsv/kitgen.py`'s `BootTable.lean`; written by
`etc/gen-rpcdriver-boottable.py` from the server command's `PkgTable.lean`, both commands having the same closure): generic in
a program's table `G` that gives every package of `rpcdriver`'s import closure its `isPkgInit`
(`KitG G`), the facts at `G` (`wf_*`) and, for the packages whose closure avoids the owned packages
(`ownedPkgs`: `rpcdriver`, net/rpc, net/http, whose first initializations return the machine's owned
resources), at `gOff S G` for `S` a sub-list of `ownedPkgs` (`wfO_*`): the table in which the packages
of `S` are not initialized yet.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.cmd.server.PkgTable

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section table
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- The table `G` with the packages of `S` not initialized (their entry `False`). -/
def gOff (S : List GoString) (G : GoString → IProp GF) : GoString → IProp GF := fun p =>
  if p ∈ S then iprop(False) else G p

theorem gOff_ne (S : List GoString) (G : GoString → IProp GF) (p : GoString) (h : p ∉ S) :
    gOff S G p = G p := by
  unfold gOff; rw [if_neg h]

theorem gOff_off (S : List GoString) (G : GoString → IProp GF) (p : GoString) (h : p ∈ S) :
    gOff S G p ⊢ iprop(False) := by
  unfold gOff; rw [if_pos h]

theorem gOff_sub (S S' : List GoString) (G : GoString → IProp GF) (h : ∀ q ∈ S', q ∈ S)
    (p : GoString) : gOff S G p ⊢ gOff S' G p := by
  unfold gOff
  by_cases h' : p ∈ S'
  · rw [if_pos (h p h'), if_pos h']
  · rw [if_neg h']
    split
    · exact false_elim
    · exact .rfl

theorem gOff_nil (G : GoString → IProp GF) : gOff [] G = G := by
  funext p; unfold gOff; simp

/-- The owned packages (the file header). -/
def ownedPkgs : List GoString :=
  [pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver, pkg_id.net.rpc, pkg_id.net.http]

/-- A program's table gives every package of `rpcdriver`'s import closure its fact. -/
structure KitG (G : GoString → IProp GF) : Prop where
  e_errors : G pkg_id.errors = isPkgInit (PROP := IProp GF) pkg_id.errors
  e_sync_atomic : G pkg_id.sync.atomic = isPkgInit (PROP := IProp GF) pkg_id.sync.atomic
  e_internal_sync : G pkg_id.internal.sync = isPkgInit (PROP := IProp GF) pkg_id.internal.sync
  e_internal_race : G pkg_id.internal.race = isPkgInit (PROP := IProp GF) pkg_id.internal.race
  e_internal_synctest : G pkg_id.internal.synctest = isPkgInit (PROP := IProp GF) pkg_id.internal.synctest
  e_sync : G pkg_id.sync = isPkgInit (PROP := IProp GF) pkg_id.sync
  e_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver_service : G pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service = isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service
  e_io : G pkg_id.io = isPkgInit (PROP := IProp GF) pkg_id.io
  e_bytes : G pkg_id.bytes = isPkgInit (PROP := IProp GF) pkg_id.bytes
  e_internal_gomodel : G pkg_id.internal.gomodel = isPkgInit (PROP := IProp GF) pkg_id.internal.gomodel
  e_internal_bytealg : G pkg_id.internal.bytealg = isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg
  e_unicode_utf8 : G pkg_id.unicode.utf8 = isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8
  e_internal_stringslite : G pkg_id.internal.stringslite = isPkgInit (PROP := IProp GF) pkg_id.internal.stringslite
  e_strings : G pkg_id.strings = isPkgInit (PROP := IProp GF) pkg_id.strings
  e_bufio : G pkg_id.bufio = isPkgInit (PROP := IProp GF) pkg_id.bufio
  e_log : G pkg_id.log = isPkgInit (PROP := IProp GF) pkg_id.log
  e_time : G pkg_id.time = isPkgInit (PROP := IProp GF) pkg_id.time
  e_context : G pkg_id.context = isPkgInit (PROP := IProp GF) pkg_id.context
  e_unsafe : G pkg_id.«unsafe» = isPkgInit (PROP := IProp GF) pkg_id.«unsafe»
  e_math_bits : G pkg_id.math.bits = isPkgInit (PROP := IProp GF) pkg_id.math.bits
  e_internal_strconv : G pkg_id.internal.strconv = isPkgInit (PROP := IProp GF) pkg_id.internal.strconv
  e_internal_oserror : G pkg_id.internal.oserror = isPkgInit (PROP := IProp GF) pkg_id.internal.oserror
  e_syscall : G pkg_id.syscall = isPkgInit (PROP := IProp GF) pkg_id.syscall
  e_io_fs : G pkg_id.io.fs = isPkgInit (PROP := IProp GF) pkg_id.io.fs
  e_internal_testlog : G pkg_id.internal.testlog = isPkgInit (PROP := IProp GF) pkg_id.internal.testlog
  e_internal_syscall_unix : G pkg_id.internal.syscall.unix = isPkgInit (PROP := IProp GF) pkg_id.internal.syscall.unix
  e_internal_poll : G pkg_id.internal.poll = isPkgInit (PROP := IProp GF) pkg_id.internal.poll
  e_os : G pkg_id.os = isPkgInit (PROP := IProp GF) pkg_id.os
  e_net : G pkg_id.net = isPkgInit (PROP := IProp GF) pkg_id.net
  e_crypto_tls : G pkg_id.crypto.tls = isPkgInit (PROP := IProp GF) pkg_id.crypto.tls
  e_strconv : G pkg_id.strconv = isPkgInit (PROP := IProp GF) pkg_id.strconv
  e_internal_abi : G pkg_id.internal.abi = isPkgInit (PROP := IProp GF) pkg_id.internal.abi
  e_reflect : G pkg_id.reflect = isPkgInit (PROP := IProp GF) pkg_id.reflect
  e_fmt : G pkg_id.fmt = isPkgInit (PROP := IProp GF) pkg_id.fmt
  e_net_http_internal_ascii : G pkg_id.net.http.internal.ascii = isPkgInit (PROP := IProp GF) pkg_id.net.http.internal.ascii
  e_net_url : G pkg_id.net.url = isPkgInit (PROP := IProp GF) pkg_id.net.url
  e_cmp : G pkg_id.cmp = isPkgInit (PROP := IProp GF) pkg_id.cmp
  e_iter : G pkg_id.iter = isPkgInit (PROP := IProp GF) pkg_id.iter
  e_slices : G pkg_id.slices = isPkgInit (PROP := IProp GF) pkg_id.slices
  e_vendor_golang_org_x_net_http_httpguts : G pkg_id.vendor.golang_org.x.net.http.httpguts = isPkgInit (PROP := IProp GF) pkg_id.vendor.golang_org.x.net.http.httpguts
  e_net_textproto : G pkg_id.net.textproto = isPkgInit (PROP := IProp GF) pkg_id.net.textproto
  e_mime_multipart : G pkg_id.mime.multipart = isPkgInit (PROP := IProp GF) pkg_id.mime.multipart
  e_math : G pkg_id.math = isPkgInit (PROP := IProp GF) pkg_id.math
  e_path : G pkg_id.path = isPkgInit (PROP := IProp GF) pkg_id.path
  e_sort : G pkg_id.sort = isPkgInit (PROP := IProp GF) pkg_id.sort
  e_internal_runtime_sys : G pkg_id.internal.runtime.sys = isPkgInit (PROP := IProp GF) pkg_id.internal.runtime.sys
  e_internal_runtime_atomic : G pkg_id.internal.runtime.atomic = isPkgInit (PROP := IProp GF) pkg_id.internal.runtime.atomic
  e_runtime : G pkg_id.runtime = isPkgInit (PROP := IProp GF) pkg_id.runtime
  e_net_http : G pkg_id.net.http = isPkgInit (PROP := IProp GF) pkg_id.net.http
  e_go_token : G pkg_id.go.token = isPkgInit (PROP := IProp GF) pkg_id.go.token
  e_net_rpc : G pkg_id.net.rpc = isPkgInit (PROP := IProp GF) pkg_id.net.rpc
  e_github_com_goose_lang_primitive : G pkg_id.github_com.goose_lang.primitive = isPkgInit (PROP := IProp GF) pkg_id.github_com.goose_lang.primitive
  e_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver : G pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver = isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

theorem wf_errors {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.errors G :=
  And.intro h.e_errors True.intro

theorem wf_sync_atomic {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.sync.atomic G :=
  And.intro h.e_sync_atomic True.intro

theorem wf_internal_sync {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.sync G :=
  And.intro h.e_internal_sync True.intro

theorem wf_internal_race {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.race G :=
  And.intro h.e_internal_race True.intro

theorem wf_internal_synctest {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.synctest G :=
  And.intro h.e_internal_synctest True.intro

theorem wf_sync {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.sync G :=
  And.intro h.e_sync ⟨wf_sync_atomic h, wf_internal_sync h, wf_internal_race h, wf_internal_synctest h, True.intro⟩

theorem wf_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver_service {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service G :=
  And.intro h.e_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver_service ⟨wf_errors h, wf_sync h, True.intro⟩

theorem wf_io {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.io G :=
  And.intro h.e_io ⟨wf_errors h, wf_sync h, True.intro⟩

theorem wf_bytes {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.bytes G :=
  And.intro h.e_bytes ⟨wf_errors h, wf_io h, True.intro⟩

theorem wf_internal_gomodel {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.gomodel G :=
  And.intro h.e_internal_gomodel True.intro

theorem wf_internal_bytealg {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.bytealg G :=
  And.intro h.e_internal_bytealg ⟨wf_internal_gomodel h, True.intro⟩

theorem wf_unicode_utf8 {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.unicode.utf8 G :=
  And.intro h.e_unicode_utf8 True.intro

theorem wf_internal_stringslite {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.stringslite G :=
  And.intro h.e_internal_stringslite ⟨wf_internal_bytealg h, True.intro⟩

theorem wf_strings {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.strings G :=
  And.intro h.e_strings ⟨wf_internal_gomodel h, wf_internal_bytealg h, wf_unicode_utf8 h, wf_internal_stringslite h, wf_io h, wf_sync h, True.intro⟩

theorem wf_bufio {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.bufio G :=
  And.intro h.e_bufio ⟨wf_bytes h, wf_errors h, wf_io h, wf_strings h, True.intro⟩

theorem wf_log {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.log G :=
  And.intro h.e_log ⟨wf_sync h, True.intro⟩

theorem wf_time {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.time G :=
  And.intro h.e_time ⟨wf_errors h, True.intro⟩

theorem wf_context {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.context G :=
  And.intro h.e_context ⟨wf_errors h, wf_sync h, wf_sync_atomic h, wf_time h, True.intro⟩

theorem wf_unsafe {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.«unsafe» G :=
  And.intro h.e_unsafe True.intro

theorem wf_math_bits {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.math.bits G :=
  And.intro h.e_math_bits ⟨wf_unsafe h, True.intro⟩

theorem wf_internal_strconv {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.strconv G :=
  And.intro h.e_internal_strconv ⟨wf_math_bits h, True.intro⟩

theorem wf_internal_oserror {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.oserror G :=
  And.intro h.e_internal_oserror ⟨wf_errors h, True.intro⟩

theorem wf_syscall {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.syscall G :=
  And.intro h.e_syscall ⟨wf_sync h, wf_errors h, wf_internal_strconv h, wf_internal_oserror h, True.intro⟩

theorem wf_io_fs {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.io.fs G :=
  And.intro h.e_io_fs ⟨wf_time h, wf_internal_oserror h, wf_errors h, wf_io h, True.intro⟩

theorem wf_internal_testlog {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.testlog G :=
  And.intro h.e_internal_testlog ⟨wf_sync h, True.intro⟩

theorem wf_internal_syscall_unix {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.syscall.unix G :=
  And.intro h.e_internal_syscall_unix ⟨wf_syscall h, True.intro⟩

theorem wf_internal_poll {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.poll G :=
  And.intro h.e_internal_poll ⟨wf_internal_syscall_unix h, wf_sync h, wf_syscall h, wf_errors h, True.intro⟩

theorem wf_os {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.os G :=
  And.intro h.e_os ⟨wf_io h, wf_io_fs h, wf_sync h, wf_syscall h, wf_internal_testlog h, wf_internal_poll h, wf_errors h, True.intro⟩

theorem wf_net {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.net G :=
  And.intro h.e_net ⟨wf_context h, wf_errors h, wf_syscall h, wf_os h, wf_time h, wf_io h, wf_internal_poll h, True.intro⟩

theorem wf_crypto_tls {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.crypto.tls G :=
  And.intro h.e_crypto_tls True.intro

theorem wf_strconv {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.strconv G :=
  And.intro h.e_strconv ⟨wf_errors h, wf_internal_strconv h, wf_internal_stringslite h, wf_unicode_utf8 h, True.intro⟩

theorem wf_internal_abi {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.abi G :=
  And.intro h.e_internal_abi True.intro

theorem wf_reflect {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.reflect G :=
  And.intro h.e_reflect ⟨wf_internal_abi h, True.intro⟩

theorem wf_fmt {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.fmt G :=
  And.intro h.e_fmt ⟨wf_errors h, wf_strconv h, wf_unicode_utf8 h, wf_io h, wf_reflect h, wf_sync h, True.intro⟩

theorem wf_net_http_internal_ascii {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.net.http.internal.ascii G :=
  And.intro h.e_net_http_internal_ascii True.intro

theorem wf_net_url {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.net.url G :=
  And.intro h.e_net_url ⟨wf_strings h, True.intro⟩

theorem wf_cmp {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.cmp G :=
  And.intro h.e_cmp True.intro

theorem wf_iter {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.iter G :=
  And.intro h.e_iter True.intro

theorem wf_slices {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.slices G :=
  And.intro h.e_slices ⟨wf_cmp h, wf_iter h, wf_math_bits h, True.intro⟩

theorem wf_vendor_golang_org_x_net_http_httpguts {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.vendor.golang_org.x.net.http.httpguts G :=
  And.intro h.e_vendor_golang_org_x_net_http_httpguts True.intro

theorem wf_net_textproto {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.net.textproto G :=
  And.intro h.e_net_textproto True.intro

theorem wf_mime_multipart {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.mime.multipart G :=
  And.intro h.e_mime_multipart ⟨wf_net_textproto h, True.intro⟩

theorem wf_math {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.math G :=
  And.intro h.e_math True.intro

theorem wf_path {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.path G :=
  And.intro h.e_path ⟨wf_errors h, wf_internal_bytealg h, True.intro⟩

theorem wf_sort {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.sort G :=
  And.intro h.e_sort ⟨wf_math_bits h, wf_slices h, True.intro⟩

theorem wf_internal_runtime_sys {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.runtime.sys G :=
  And.intro h.e_internal_runtime_sys True.intro

theorem wf_internal_runtime_atomic {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.internal.runtime.atomic G :=
  And.intro h.e_internal_runtime_atomic True.intro

theorem wf_runtime {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.runtime G :=
  And.intro h.e_runtime ⟨wf_internal_runtime_sys h, wf_internal_runtime_atomic h, True.intro⟩

theorem wf_net_http {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.net.http G :=
  And.intro h.e_net_http ⟨wf_context h, wf_crypto_tls h, wf_errors h, wf_fmt h, wf_io h, wf_log h, wf_net_http_internal_ascii h, wf_net_url h, wf_slices h, wf_strings h, wf_sync h, wf_sync_atomic h, wf_time h, wf_vendor_golang_org_x_net_http_httpguts h, wf_net h, wf_mime_multipart h, wf_net_textproto h, wf_strconv h, wf_math h, wf_path h, wf_sort h, wf_bufio h, wf_runtime h, True.intro⟩

theorem wf_go_token {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.go.token G :=
  And.intro h.e_go_token True.intro

theorem wf_net_rpc {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.net.rpc G :=
  And.intro h.e_net_rpc ⟨wf_bufio h, wf_errors h, wf_io h, wf_log h, wf_net h, wf_net_http h, wf_sync h, wf_go_token h, True.intro⟩

theorem wf_github_com_goose_lang_primitive {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.github_com.goose_lang.primitive G :=
  And.intro h.e_github_com_goose_lang_primitive True.intro

theorem wf_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver {G : GoString → IProp GF} (h : KitG G) :
    GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver G :=
  And.intro h.e_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver ⟨wf_errors h, wf_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver_service h, wf_net_rpc h, wf_net h, wf_net_http h, wf_strings h, wf_sync h, wf_github_com_goose_lang_primitive h, True.intro⟩

theorem wfO_errors {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.errors (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.errors ∉ ownedPkgs) (hS _ hm))).trans
    h.e_errors) True.intro

theorem wfO_sync_atomic {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.sync.atomic (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.sync.atomic ∉ ownedPkgs) (hS _ hm))).trans
    h.e_sync_atomic) True.intro

theorem wfO_internal_sync {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.sync (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.sync ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_sync) True.intro

theorem wfO_internal_race {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.race (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.race ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_race) True.intro

theorem wfO_internal_synctest {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.synctest (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.synctest ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_synctest) True.intro

theorem wfO_sync {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.sync (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.sync ∉ ownedPkgs) (hS _ hm))).trans
    h.e_sync) ⟨wfO_sync_atomic h S hS, wfO_internal_sync h S hS, wfO_internal_race h S hS, wfO_internal_synctest h S hS, True.intro⟩

theorem wfO_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver_service {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service ∉ ownedPkgs) (hS _ hm))).trans
    h.e_github_com_mit_pdos_etcd_grove_examples_net_rpcdriver_service) ⟨wfO_errors h S hS, wfO_sync h S hS, True.intro⟩

theorem wfO_io {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.io (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.io ∉ ownedPkgs) (hS _ hm))).trans
    h.e_io) ⟨wfO_errors h S hS, wfO_sync h S hS, True.intro⟩

theorem wfO_bytes {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.bytes (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.bytes ∉ ownedPkgs) (hS _ hm))).trans
    h.e_bytes) ⟨wfO_errors h S hS, wfO_io h S hS, True.intro⟩

theorem wfO_internal_gomodel {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.gomodel (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.gomodel ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_gomodel) True.intro

theorem wfO_internal_bytealg {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.bytealg (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.bytealg ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_bytealg) ⟨wfO_internal_gomodel h S hS, True.intro⟩

theorem wfO_unicode_utf8 {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.unicode.utf8 (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.unicode.utf8 ∉ ownedPkgs) (hS _ hm))).trans
    h.e_unicode_utf8) True.intro

theorem wfO_internal_stringslite {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.stringslite (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.stringslite ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_stringslite) ⟨wfO_internal_bytealg h S hS, True.intro⟩

theorem wfO_strings {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.strings (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.strings ∉ ownedPkgs) (hS _ hm))).trans
    h.e_strings) ⟨wfO_internal_gomodel h S hS, wfO_internal_bytealg h S hS, wfO_unicode_utf8 h S hS, wfO_internal_stringslite h S hS, wfO_io h S hS, wfO_sync h S hS, True.intro⟩

theorem wfO_bufio {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.bufio (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.bufio ∉ ownedPkgs) (hS _ hm))).trans
    h.e_bufio) ⟨wfO_bytes h S hS, wfO_errors h S hS, wfO_io h S hS, wfO_strings h S hS, True.intro⟩

theorem wfO_log {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.log (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.log ∉ ownedPkgs) (hS _ hm))).trans
    h.e_log) ⟨wfO_sync h S hS, True.intro⟩

theorem wfO_time {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.time (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.time ∉ ownedPkgs) (hS _ hm))).trans
    h.e_time) ⟨wfO_errors h S hS, True.intro⟩

theorem wfO_context {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.context (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.context ∉ ownedPkgs) (hS _ hm))).trans
    h.e_context) ⟨wfO_errors h S hS, wfO_sync h S hS, wfO_sync_atomic h S hS, wfO_time h S hS, True.intro⟩

theorem wfO_unsafe {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.«unsafe» (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.«unsafe» ∉ ownedPkgs) (hS _ hm))).trans
    h.e_unsafe) True.intro

theorem wfO_math_bits {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.math.bits (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.math.bits ∉ ownedPkgs) (hS _ hm))).trans
    h.e_math_bits) ⟨wfO_unsafe h S hS, True.intro⟩

theorem wfO_internal_strconv {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.strconv (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.strconv ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_strconv) ⟨wfO_math_bits h S hS, True.intro⟩

theorem wfO_internal_oserror {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.oserror (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.oserror ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_oserror) ⟨wfO_errors h S hS, True.intro⟩

theorem wfO_syscall {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.syscall (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.syscall ∉ ownedPkgs) (hS _ hm))).trans
    h.e_syscall) ⟨wfO_sync h S hS, wfO_errors h S hS, wfO_internal_strconv h S hS, wfO_internal_oserror h S hS, True.intro⟩

theorem wfO_io_fs {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.io.fs (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.io.fs ∉ ownedPkgs) (hS _ hm))).trans
    h.e_io_fs) ⟨wfO_time h S hS, wfO_internal_oserror h S hS, wfO_errors h S hS, wfO_io h S hS, True.intro⟩

theorem wfO_internal_testlog {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.testlog (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.testlog ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_testlog) ⟨wfO_sync h S hS, True.intro⟩

theorem wfO_internal_syscall_unix {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.syscall.unix (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.syscall.unix ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_syscall_unix) ⟨wfO_syscall h S hS, True.intro⟩

theorem wfO_internal_poll {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.poll (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.poll ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_poll) ⟨wfO_internal_syscall_unix h S hS, wfO_sync h S hS, wfO_syscall h S hS, wfO_errors h S hS, True.intro⟩

theorem wfO_os {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.os (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.os ∉ ownedPkgs) (hS _ hm))).trans
    h.e_os) ⟨wfO_io h S hS, wfO_io_fs h S hS, wfO_sync h S hS, wfO_syscall h S hS, wfO_internal_testlog h S hS, wfO_internal_poll h S hS, wfO_errors h S hS, True.intro⟩

theorem wfO_net {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.net (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.net ∉ ownedPkgs) (hS _ hm))).trans
    h.e_net) ⟨wfO_context h S hS, wfO_errors h S hS, wfO_syscall h S hS, wfO_os h S hS, wfO_time h S hS, wfO_io h S hS, wfO_internal_poll h S hS, True.intro⟩

theorem wfO_crypto_tls {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.crypto.tls (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.crypto.tls ∉ ownedPkgs) (hS _ hm))).trans
    h.e_crypto_tls) True.intro

theorem wfO_strconv {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.strconv (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.strconv ∉ ownedPkgs) (hS _ hm))).trans
    h.e_strconv) ⟨wfO_errors h S hS, wfO_internal_strconv h S hS, wfO_internal_stringslite h S hS, wfO_unicode_utf8 h S hS, True.intro⟩

theorem wfO_internal_abi {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.abi (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.abi ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_abi) True.intro

theorem wfO_reflect {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.reflect (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.reflect ∉ ownedPkgs) (hS _ hm))).trans
    h.e_reflect) ⟨wfO_internal_abi h S hS, True.intro⟩

theorem wfO_fmt {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.fmt (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.fmt ∉ ownedPkgs) (hS _ hm))).trans
    h.e_fmt) ⟨wfO_errors h S hS, wfO_strconv h S hS, wfO_unicode_utf8 h S hS, wfO_io h S hS, wfO_reflect h S hS, wfO_sync h S hS, True.intro⟩

theorem wfO_net_http_internal_ascii {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.net.http.internal.ascii (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.net.http.internal.ascii ∉ ownedPkgs) (hS _ hm))).trans
    h.e_net_http_internal_ascii) True.intro

theorem wfO_net_url {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.net.url (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.net.url ∉ ownedPkgs) (hS _ hm))).trans
    h.e_net_url) ⟨wfO_strings h S hS, True.intro⟩

theorem wfO_cmp {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.cmp (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.cmp ∉ ownedPkgs) (hS _ hm))).trans
    h.e_cmp) True.intro

theorem wfO_iter {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.iter (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.iter ∉ ownedPkgs) (hS _ hm))).trans
    h.e_iter) True.intro

theorem wfO_slices {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.slices (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.slices ∉ ownedPkgs) (hS _ hm))).trans
    h.e_slices) ⟨wfO_cmp h S hS, wfO_iter h S hS, wfO_math_bits h S hS, True.intro⟩

theorem wfO_vendor_golang_org_x_net_http_httpguts {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.vendor.golang_org.x.net.http.httpguts (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.vendor.golang_org.x.net.http.httpguts ∉ ownedPkgs) (hS _ hm))).trans
    h.e_vendor_golang_org_x_net_http_httpguts) True.intro

theorem wfO_net_textproto {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.net.textproto (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.net.textproto ∉ ownedPkgs) (hS _ hm))).trans
    h.e_net_textproto) True.intro

theorem wfO_mime_multipart {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.mime.multipart (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.mime.multipart ∉ ownedPkgs) (hS _ hm))).trans
    h.e_mime_multipart) ⟨wfO_net_textproto h S hS, True.intro⟩

theorem wfO_math {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.math (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.math ∉ ownedPkgs) (hS _ hm))).trans
    h.e_math) True.intro

theorem wfO_path {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.path (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.path ∉ ownedPkgs) (hS _ hm))).trans
    h.e_path) ⟨wfO_errors h S hS, wfO_internal_bytealg h S hS, True.intro⟩

theorem wfO_sort {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.sort (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.sort ∉ ownedPkgs) (hS _ hm))).trans
    h.e_sort) ⟨wfO_math_bits h S hS, wfO_slices h S hS, True.intro⟩

theorem wfO_internal_runtime_sys {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.runtime.sys (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.runtime.sys ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_runtime_sys) True.intro

theorem wfO_internal_runtime_atomic {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.internal.runtime.atomic (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.internal.runtime.atomic ∉ ownedPkgs) (hS _ hm))).trans
    h.e_internal_runtime_atomic) True.intro

theorem wfO_runtime {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.runtime (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.runtime ∉ ownedPkgs) (hS _ hm))).trans
    h.e_runtime) ⟨wfO_internal_runtime_sys h S hS, wfO_internal_runtime_atomic h S hS, True.intro⟩

theorem wfO_go_token {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.go.token (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.go.token ∉ ownedPkgs) (hS _ hm))).trans
    h.e_go_token) True.intro

theorem wfO_github_com_goose_lang_primitive {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) : GetIsPkgInitProp pkg_id.github_com.goose_lang.primitive (gOff S G) :=
  And.intro ((gOff_ne S G _ (fun hm => (by decide : pkg_id.github_com.goose_lang.primitive ∉ ownedPkgs) (hS _ hm))).trans
    h.e_github_com_goose_lang_primitive) True.intro

/-- net/http's facts at a table in which it is initialized (its imports avoid the owned packages). -/
theorem wfX_net_http {G : GoString → IProp GF} (h : KitG G) (S : List GoString)
    (hS : ∀ q ∈ S, q ∈ ownedPkgs) (hn : pkg_id.net.http ∉ S) : GetIsPkgInitProp pkg_id.net.http (gOff S G) :=
  And.intro ((gOff_ne S G _ hn).trans h.e_net_http) ⟨wfO_context h S hS, wfO_crypto_tls h S hS, wfO_errors h S hS, wfO_fmt h S hS, wfO_io h S hS, wfO_log h S hS, wfO_net_http_internal_ascii h S hS, wfO_net_url h S hS, wfO_slices h S hS, wfO_strings h S hS, wfO_sync h S hS, wfO_sync_atomic h S hS, wfO_time h S hS, wfO_vendor_golang_org_x_net_http_httpguts h S hS, wfO_net h S hS, wfO_mime_multipart h S hS, wfO_net_textproto h S hS, wfO_strconv h S hS, wfO_math h S hS, wfO_path h S hS, wfO_sort h S hS, wfO_bufio h S hS, wfO_runtime h S hS, True.intro⟩

end table

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
