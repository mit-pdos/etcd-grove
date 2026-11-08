# k8s 7e-3b: the Go model's functions proved: plan and state (2026-11-08, branch `k8s-7e`)

Stage 7e-3b of `notes/k8s-7e-scope.md`: prove 7e-0's driver model functions against the pure model
(`ListModel.lean`, 7e-3a, and `KModel`/`KSteps` extended). The driver proofs it breaks stay broken
on the branch until 7e-4.

## Done

- The driver's translation is regenerated: `etc/goose.py --project k8s-apiserver`, 2 files
  (`Code/.../examples/k8s/etcd3.lean`, `GeneratedProof/...`).
- `Base.lean`: `errNoList` dropped from the package fact (the variable is gone). `etc/gen-init.py`
  still has to be rerun for the driver (`--check` first).

## (a) The object layer: done (2026-11-08)

Builds (targeted `lake build`, no `sorry`): `Codec`, `ObjSpec`, `Contract`, `Callbacks`, `Init`
(regenerated: `etc/gen-init.py`'s `_K8E` drops `errNoList`), and the spec/proof pairs `putField`
(new), `encodeWith`, `encodeObj`, `encodeV0`, `getField` (new), `decodeObj`, `codec.Encode`,
`decoder.Decode`, `versioner.{UpdateObject,PrepareObjectForStorage,ObjectResourceVersion}`,
`Obj.{GetUID,GetResourceVersion}`, `validateFor`, `splitKey` (new), `updated`, `tryUpdateFor`.
- `DObj` is a structure of the six fields with their length bounds; `o.toObj n` is Go's record
  (an `abbrev`, so its projections reduce). The Go functions' specs are stated on the record
  (`v : Obj`), not field by field, so they no longer change with the record's fields.
- The codec on the record: `putF`/`encodeWith tag v`, `getFieldD`/`decodeD d : Option Obj`;
  `decodeD_encode` (either tag), `decodeD_some` (fits, RV 0, same length as re-encoded: the no-op
  update's bound), `encodeWith_v0_ne_v1` (D30g's seeds are non-canonical), `encodeWith_length`.
- `getField.spec` takes `i < 2^16` (no overflow of `i+1+n`; `decodeObj`'s indices are below
  `3 + 5*256`).
- Callbacks reject on the node: `rejects has reject node`; `updGo` (on the record) and `updObj`
  (on `DObj`, `updObj_toObj` under `inFits`: key, node, app shorter than 256);
  `tryUpdateFor.spec`'s premise is `inFits inp`.
- **`strings.Cut`** (untranslated in Perennial) is used by `splitKey`: `Spec/strings/Cut.lean`
  (`cutL`) is taken as a **hypothesis** of `splitKey.wp_proof`, no axiom. For 7e-2's Draft, with
  the other out-of-driver callee specs.

## What breaks first, and the order

The breakage starts in the object layer, which `KModel.lean` imports through `Callbacks`. So
7e-3b has to begin with the object layer, which the Scope counted under 7e-4:
1. **Objects** (`ObjSpec`, `Codec`, `Contract`):
   - `DObj` gains the namespace, node and app;
   - `objAtD`'s `Obj.mk` takes 7 fields;
   - `encodeWith`/`putField`/`getField`/`decodeObj` are the new length-prefixed codec, and
     `driverCodec`'s round trip and non-canonical seeds (D30g) are redone;
   - `objLabels` and the metav1 accessors (`GetNamespace`, `GetLabels`).
   - First errors: `ObjSpec.lean:88` (`Obj.mk` arity) and `:119`.
2. **Callbacks**: `validateFor(rejects, reject)` and `updated` on the node, with
   `splitKey`/`strings.Cut` and app/node set.
3. **`KModel`/`KSteps`/`ItemList`/`MDefs`**:
   - the records: `Obj` 7 fields, `Input` 27, `Output` 15;
   - `mcreateL`, `mgetL` (`ETooLarge`), `sameObjL`, `objOutL`, `isWriteL` (explicit kinds);
   - `mcfg` with `hist`, and `stepL` with lists;
   - `CfgEquiv`/`setOf` with `hist`.
4. **The new functions**, each a spec and proof file:
   - `pastRead`, `keyInScope` (`strings.HasPrefix`/`TrimSuffix` specs);
   - `histLen`, `appendHist`, `histOf`, `histAt`, `histEqual`, `advance`;
   - `fieldSel.{Matches,Empty,RequiresExactMatch,Transform,Requirements,String,DeepCopySelector}`;
   - the same `labelSel` methods;
   - `getAttrs`, `fieldSelFor`, `predicate`, `matchOpt`, `listOptions`;
   - `objOf`, `outEqual` (items loop), `configEqual` (`histEqual`), `closure`/`step`/`Model` with
     `hist`, `genList`/`genFrom`;
   - `mlist`.

## Two design points found while scoping the proofs (for 81)

- **`Output` now holds a slice** (`Items []Obj`), and `mcfg` a pointer chain (`hist *hnode`).
  - Porcupine's model specs (`k8setcd3S`: `decOp`, `ioOk`, `stRepB`) assume outputs are plain Go
    values decoded purely.
  - With lists, `ioOk` must carry the items' read-only points-to (`y.Items ↦*□ its`), and
    `decOp` must read them through it.
  - The state's `rep` must own the history chain, read-only (`hnode` cells `↦□`, so shared
    tails stay shareable).
  - Both are statements of the porcupine instance (`MDefs.lean`), not trusted text, but they
    change `k8setcd3S`.
- **`mlist`'s callees outside the driver**:
  - `storage.PrepareKey` (translated: provable);
  - `storage.PrepareContinueToken` → `EncodeContinue` (JSON/base64): the `encL` trust boundary of
    the Scope, a 7e-2 Draft item (a hard stop);
  - `SelectionPredicate.Matches`/`Empty` (translated in `storage`: provable over the driver's
    selector specs);
  - `fields.Set.Get`/`labels.Set.Has`/`Get` (apimachinery, translated or names-only:
    to check).
  - 7e-3b can prove `mlist` taking these specs as hypotheses (the spec/proof discipline). Their
    statements, `encL` included, then go to 7e-2's Draft for review before anything links.

## Size

The object layer is about 900 lines today (ObjSpec 139, Codec 248, Contract 348, Callbacks 201),
mostly redone. 7e-3b proper is the Scope's estimate, 1200-1800 lines. Expect about 2000-2700
lines for the two together.
