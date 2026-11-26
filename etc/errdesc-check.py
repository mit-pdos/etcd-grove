#!/usr/bin/env python3
"""Check that every trusted statement about an error's description is reviewed for stability.

An error's description (`descIs`) and code (`statusCodeIs`) are per-run relations (errdesc stages 2a/2b,
2026-11-20/21; until then the pure `errDesc`/`statusCode`, Lean functions of the error value), true of
Go only for an error whose `Error()` and `GRPCStatus()` return the same on every call
(`notes/decisions.md`, "`status.FromError`: an error's description from a stable `Error()`";
`examples/axiomcx/flipdesc` on branch `axiom/invoker-filled` refuted the version without it). A
trusted statement (an axiom, or the spec of a function whose proof is an axiom) that mentions the
description, the code, or the predicates that carry stability (`statusErrOk`, `errorMsgIs`,
`grpcErrMethodsOk`, `errMsgOk`, `fmt.modelErrIs`/`wrapErrIs`) is listed below with why it is true
of Go; a new one fails this check until it is reviewed and added. A cheap check, not a proof: it
reads names, not terms.

usage: etc/errdesc-check.py   (exit 1 on an unreviewed statement)
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

NAMES = re.compile(r'\b(errDesc|statusCode|statusErrOk|errorMsgIs|grpcErrMethodsOk|errMsgOk|'
                   r'modelErrIs|wrapErrIs|descIs|statusAt|statusCodeIs|handlerErrOut|notHandlerErr)\b')

# file (and axiom name, for an axiom declared in a proof file): why it is true of Go
REVIEWED = {
    'Spec/google_golang_org/grpc/status/FromError.lean':
        'the description and code from a stable Error()/GRPCStatus() (the premise statusErrOk)',
    'Spec/google_golang_org/grpc/status/Error.lean':
        '*status.Error: Error() formats its fixed status, GRPCStatus() returns it, Is is proto.Equal; '
        'no Format method (statusErrOk since premise-fixes-4; examples/premisefix/fmtarg); a pointer '
        'value of its pointer type (statusErrOk\'s stTypedErr since #45, Go\'s typing)',
    'Spec/google_golang_org/grpc/status/Code.lean': 'statusErrOk a premise only',
    'Spec/google_golang_org/grpc/status/Status__Code.lean':
        'status.statusAt a premise only: the read-only status the producer built (its code returned)',
    'Spec/k8s_io/apiserver/pkg/storage/etcd3/metrics/RecordEtcdRequest.lean':
        'statusErrOk a premise only (no description or code in its post)',
    'Spec/k8s_io/apiserver/pkg/storage/etcd3/metrics/OperationLatencyTracker__Record.lean':
        'statusErrOk a premise only (no description or code in its post; as RecordEtcdRequest, whose '
        'errorReason Record shares): the caller proves it, store.Get from Client.Get\'s post '
        '(statusErrOk_split); prove-metrics 2026-11-21, examples/premisefix/latencytracker',
    'Spec/fmt/ErrorfWrap.lean':
        "the model's errorString cell and Go's wrapError msg are written once; the errDesc prefix "
        "only given an Unwrap method (Go's wrapError; H0, 2026-11-18: vacuous of the model's error)",
    'Spec/go_etcd_io/etcd/client/v3/Client__Endpoints.lean': 'statusErrOk opened, not used',
    'Spec/go_etcd_io/etcd/client/v3/withVersion.lean': 'statusErrOk opened, not used',
    'Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/KVGetDist.lean':
        "KV_Get_dist's error arm: statusErrOk err, the in-process kv.Get.spec's kvErr part; real grpc-go "
        "across a network meets it (notes/axiom-review/kv-get-dist-statuserr.md: 44 cases, 0 violations; "
        "a coordinator-approved strengthening, 2026-11-26)",
    'Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/WatchDist.lean':
        'RequestProgress_dist only (Watch_dist names none): nil, errors.New\'s "no stream found", ctx.Err() (isContext) or run\'s closeErr, a raw Recv status/io.EOF or v3rpc.Error of NewStream\'s/getToken\'s error, all built in the caller by grpc-go (cliStreamErr, peer-independent) or clientv3, the member choosing only code, message, details; real 3-member cluster, 13 failure kinds, 0 violations (notes/axiom-review/requestprogress-dist-statuserr.md)',
    # rpctypes' initializers (etc/gen-init.py): status.Error values and EtcdError values
    'Proof/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/Init.lean:*':
        'ErrGRPC*: status.Error values; Err*: EtcdError values (Error() returns desc); neither type '
        'has a Format method (examples/premisefix/fmtarg)',
}

AXIOM = re.compile(r'^axiom\s+(\S+)(.*?)(?=^\S)', re.S | re.M)


def skip(rel):
    p = rel.parts
    return (p[0] in ('.lake', 'old', 'Code', 'GeneratedProof')
            or (len(p) > 1 and p[1] in ('Code', 'GeneratedProof')))


def main():
    bad = []
    for f in sorted(ROOT.glob('**/*.lean')):
        rel = f.relative_to(ROOT)
        if skip(rel):
            continue
        s = f.read_text()
        for m in AXIOM.finditer(s):
            if NAMES.search(m.group(2)):
                key = f'{rel}:{m.group(1)}'
                if key not in REVIEWED and f'{rel}:*' not in REVIEWED:
                    bad.append(key)
        parts = rel.parts
        i = parts.index('Spec') if 'Spec' in parts[:2] else -1
        if i >= 0:
            proof = ROOT.joinpath(*parts[:i], 'Proof', *parts[i + 1:])
            if (proof.exists() and re.search(r'^axiom\s', proof.read_text(), re.M)
                    and NAMES.search(s) and str(rel) not in REVIEWED):
                bad.append(str(rel))
    for b in bad:
        print(f'errdesc-check: unreviewed trusted statement about an error description: {b}')
    if bad:
        print('errdesc-check: review it (is the error\'s Error()/GRPCStatus() stable?) and add it '
              'to REVIEWED in etc/errdesc-check.py')
        return 1
    print('errdesc-check: ok')
    return 0


if __name__ == '__main__':
    sys.exit(main())
