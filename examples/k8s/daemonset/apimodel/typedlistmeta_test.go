package apimodel_test

// Go evidence for the reflector's pending hypothesis `cache.typedListMeta`
// (Spec/k8s_io/client_go/tools/cache/typedListMeta.lean, k8s 7g follow-up (B'),
// notes/k8s-7g-listaccessor-bprime.md): for each of the reflector's four typed lists `*L`
// (`resListTy`), (1) `*L` is a `meta.List` (so `meta.ListAccessor` returns the same pointer, nil
// error), (2) `GetResourceVersion()` returns `ListMeta.ResourceVersion` and (3) `GetContinue()`
// returns `ListMeta.Continue` (`""` for the model's lists), the list unchanged.

import (
	"testing"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
)

func TestTypedListMeta(t *testing.T) {
	lm := metav1.ListMeta{ResourceVersion: "42"}
	lists := []any{
		&corev1.PodList{ListMeta: lm, Items: []corev1.Pod{{}}},
		&corev1.NodeList{ListMeta: lm},
		&appsv1.DaemonSetList{ListMeta: lm},
		&appsv1.ControllerRevisionList{ListMeta: lm, Items: []appsv1.ControllerRevision{{}}},
	}
	for _, l := range lists {
		ml, ok := l.(meta.List) // (1) the type set
		if !ok {
			t.Fatalf("%T is not a meta.List", l)
		}
		acc, err := meta.ListAccessor(l)
		if err != nil || acc != ml {
			t.Fatalf("ListAccessor(%T) = %v, %v; want the same pointer, nil", l, acc, err)
		}
		if rv := ml.GetResourceVersion(); rv != "42" { // (2)
			t.Errorf("%T.GetResourceVersion() = %q, want %q", l, rv, "42")
		}
		if c := ml.GetContinue(); c != "" { // (3)
			t.Errorf("%T.GetContinue() = %q, want empty", l, c)
		}
	}
}
