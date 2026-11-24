# Review: `bridge.New`'s precondition and a grpc address's protocols (2026-11-24)

**Target.** `axiom bridge.New.wp_proof` (`Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/New.lean`,
D26), as it stood on `lean` at `94767c2a2f`: its precondition was only `netListenerAt l a`.

**Finding (refuted).** Since phase 7 S2's interface, `net.Listen` returns `netAddrLeft a` beside the listener,
and `addr_set_proto_tok` sets `a`'s protocols from it (as `grpc.start'` does). So one program can give `a` a grpc
table and bridge `a` to a server that meets none of its specs. Found by the `axiom` skill against etcd-dist's
interim `Client_Get_dist` (`notes/putget-dist-plan.md` §12, review 4, on `dist-putget-interim/2026-11-24`
`530dc2af99`, where `etcdAddrAt a γE mid := ∃ σ, grpcAddrAt a (etcdSvc γE mid)`): the program below `Get`s through
the bridge a value the real store lacks, and its check panics.

- **Go:** `examples/axiomcx/bridgeaddrleft/` (`TestMainPanics`: `recovered: bridgeaddrleft: Get did not return v`;
  go1.27.3, `lean`'s pins; 5/5 runs on the review, 1/1 here).
- **Lean:** the sketch below (not built), over `Client_Get_dist`, `etcdSvc` and `bridge.New`.
- A second route needs no `netAddrLeft`: `etcdAddr_set` from `addrUnset a`, then `listen_au` from the `addrProto` in
  `etcdAddrAt` (or, for the earlier opaque `etcdAddrRaw`, the net part's `Listen`, which only lends the listening
  token, before `etcdAddr_set`), and `addrClaim a` from `netAddrFree a`: `netListenerAt l a` again.

**Fix** (`notes/decisions.md`, "`bridge.New` consumes what sets the bridged address's protocols"): `New` also
consumes `netAddrLeft a`. Then whoever bridges `a` has spent what sets `a`'s protocols, and whoever set them
(`netAddrLeft` or `addrUnset`, both holding `a`'s exclusive pending set) cannot form `netAddrLeft a` to bridge.
Its one caller, `cluster3.StartBridge`, passes `net.Listen`'s.

**Open (reported to the switch's owner, checked separately):** whether the same route refutes grpc's own
`ClientConn.Invoke.wp_proof` with a table the program picks, without any interim axiom.

## The proof sketch

```
/- Proof sketch (not compiled: no build of eg-pgint here) that `bridgeaddrleft.Main` does not panic, from
   `etcd_dist.Client_Get_dist.wp_proof` (A5), `etcd_dist.etcdSvc` (A1, through the definition of
   `etcdAddrAt`) and `bridge.New.wp_proof`, plus the single-process trust base every etcdstart proof
   already rests on. `bridgeaddrleft.Main` panics when run (bridgeaddrleft_test.go, 5/5 runs).

theorem bridgeaddrleft.Main.wp_proof
    (wp_StartServer : etcdstart.StartServer.spec) (wp_Serve : etcdstart.Serve.spec)
    (wp_Listen : net.Listen.spec)                      -- Spec/net/Listen.lean (proved)
    (wp_bridgeNew : bridge.New.spec)                   -- axiom bridge.New.wp_proof
    (wp_NewClient : etcdstart.NewClient.spec) (hWT : context.WithTimeoutBackground.spec)
    (wp_Get_dist : ∀ [HasExt netExt], etcd_dist.Client_Get_dist.spec) :
  {{ isPkgInit bridgeaddrleft ∗ netAddrFree peerB ∗ netAddrFree clientB ∗ netAddrFree addrA ∗ <start's other rights> }}
    @! bridgeaddrleft.Main #() {{ RET #(); True }}

 1. StartServer / Serve(s, clientB): exactly examples/etcd/putget's Main proof (netAddrFree clientB).
    Any error -> return.  (The real etcd at clientB is all Go needs; the proof uses only the specs.)
 2. l, err := net.Listen("tcp", addrA): wp_Listen with netAddrFree addrA.
      ok: netListenerAt l addrA ∗ netAddrLeft addrA.        err: return.
 3. Ghost, all proved laws (this is what 530dc2af99 makes possible: etcdAddrAt is now a definition):
      icases netAddrLeft addrA ⟨%hX, Hpend, #Htok, #HlisInv⟩; haveI := hX
      imod netProto_alloc ⊤ with ⟨%π, #Hreg⟩
      imod depSlots_alloc ⊤ with ⟨%σ, #Hs⟩
      imod addr_set_proto_tok ⊤ addrA (grpcCliPI (etcdSvc γE 0)) (grpcSrvPI (etcdSvc γE 0))
           $$ Hreg Hpend Htok HlisInv with #Hp
      -- Hp ∗ Hs  is  grpcAddrAt addrA (etcdSvc γE 0), so  #Ha : etcdAddrAt addrA γE 0
    with γE and the KV state fabricated:
      imod ghostVar_alloc σ0 with γst        -- σ0.kvs = [⟨"k","v",…⟩]  (sorted, findKey "k" = "v")
      imod monoNat_alloc 1 with γf; lb #Hf1 : monoNatLbOwn γf 1
      γr := { (default : ReadNames) with kv := { … with st := γst } }
      imod inv_alloc kvClientN (∃ σ n, etcdKV γr.kv σ ∗ monoNatAuthOwn γf 1 n ∗ ⌜putGetOk "k" "v" σ n⌝)
        -- #HI : putGetInv γr γf "k" "v"   (half of γst inside, the other half dropped)
      imod envPub_start ⊤ (fun _ => True) with ⟨%γE, Hh, #Hpub⟩
      imod env_publish ⊤ γE _ (fun _ => True) ⟨γst⟩ $$ Hh Hpub [] with #HνE   -- envAt γE ⟨γst⟩
    (order: allocate γE before step 3's addr_set_proto_tok; both are ghost.)
 4. bridge.New(clientB, l): wp_bridgeNew clientB addrA l with netListenerAt l addrA. Post dropped.
 5. cli, err := etcdstart.NewClient(addrA, lg): isNewClient cli [addrA] V ∗ clientNoProxy cli
    (plainEndpoint "127.0.0.1:23822").
 6. gctx := WithTimeout(...): as dist/putget/Client.lean:150-156.
 7. resp, err := cli.Get(gctx, "k"):
      wp_Get_dist (π := π) cli addrA V γE 0 ⟨γst⟩ γr γf ci cd "k" "v" slice.nil
        (opSizeOk (opGetModel "k" []) : by decide/compute) rfl
        $$ [pkg init, isNewClient, clientNoProxy, Ha, HνE, ctx, optsAt nil, HI, Hf1]
      post: err = nil ∗ rangeRespMsg resp m ∗ ⌜m.kvs.head?.map value = some "v"⌝   or err ≠ nil.
 8. The check: dist/putget/Client.lean:173-217 verbatim (len(resp.Kvs) ≥ 1, Kvs[0].Value = "v"):
    the panic branch is refuted by the pure fact.                                                   ∎

#print axioms would add, over the single-process base: etcd_dist.etcdSvc,
etcd_dist.Client_Get_dist.wp_proof, bridge.New.wp_proof.

Variant without net.Listen's leftover (route B): etcdAddr_set from addrUnset addrA (keeping addrClaim addrA
from netAddrFree addrA), then Net's canonical Listen.spec_addrOk with listen_au (from the addrProto inside
etcdAddrAt) gives netLis l addrA true ∗ netLisAt l addrA = netListenerOpen l addrA; with addrClaim addrA that
is netListenerAt l addrA, and step 4 on.

Variant refuting A4 instead (A5 used soundly): M1 a real dist member at b1 (Serve_dist, its genuine γE1,
mid1), a second real etcd at b2, addrA's table set to etcdSvc γE1 mid1 by step 3, bridge addrA -> b2;
Put("k","v") via addrA (A4: nil => M1's putGetInv flag 1), Get via b1 (A5 on M1's real address): Go reads
M1's empty store and panics.
-/
```
