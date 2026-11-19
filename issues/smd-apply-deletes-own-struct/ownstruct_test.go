package merge_test

import (
	"testing"

	"sigs.k8s.io/structured-merge-diff/v7/fieldpath"
	"sigs.k8s.io/structured-merge-diff/v7/merge"
	"sigs.k8s.io/structured-merge-diff/v7/schema"
	"sigs.k8s.io/structured-merge-diff/v7/typed"
	"sigs.k8s.io/structured-merge-diff/v7/value"
)

type osIdentityConverter struct{}

func (osIdentityConverter) Convert(o *typed.TypedValue, _ fieldpath.APIVersion) (*typed.TypedValue, error) {
	return o, nil
}
func (osIdentityConverter) IsMissingVersionError(error) bool { return false }

// TestReapplyDeletesOwnStruct: manager A applied `spec: {}` and owns `.spec`. The live object's
// spec also holds a field nobody owns (`a`, as one the API server defaulted) and an empty
// associative list (`l: []`). A applies `spec: {}` again: the result has no spec at all, although
// A applies it now. Without `l: []` the same apply is a no-op.
func TestReapplyDeletesOwnStruct(t *testing.T) {
	s := schema.String
	ref := func(name string) schema.TypeRef { return schema.TypeRef{NamedType: &name} }
	sc := &schema.Schema{Types: []schema.TypeDef{
		{Name: "root", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "name", Type: ref("string")},
			{Name: "spec", Type: ref("spec")},
		}}}},
		{Name: "spec", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "a", Type: ref("string")},
			{Name: "l", Type: ref("items")},
		}}}},
		{Name: "item", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "name", Type: ref("string")},
		}}}},
		{Name: "items", Atom: schema.Atom{List: &schema.List{
			ElementType: ref("item"), ElementRelationship: schema.Associative, Keys: []string{"name"}}}},
		{Name: "string", Atom: schema.Atom{Scalar: &s}},
	}}
	rootName := "root"
	typed := func(o map[string]interface{}) *typed.TypedValue {
		tv, err := typed.AsTyped(value.NewValueInterface(o), sc, schema.TypeRef{NamedType: &rootName})
		if err != nil {
			t.Fatal(err)
		}
		return tv
	}
	for _, spec := range []map[string]interface{}{
		{"a": "a"},
		{"a": "a", "l": []interface{}{}},
	} {
		managers := fieldpath.ManagedFields{
			"A": fieldpath.NewVersionedSet(fieldpath.NewSet(fieldpath.MakePathOrDie("spec")), "v1", true),
			"B": fieldpath.NewVersionedSet(fieldpath.NewSet(fieldpath.MakePathOrDie("name")), "v1", true),
		}
		live := typed(map[string]interface{}{"name": "o", "spec": spec})
		config := typed(map[string]interface{}{"spec": map[string]interface{}{}})
		updater := (&merge.UpdaterBuilder{Converter: osIdentityConverter{}}).BuildUpdater()
		obj, _, err := updater.Apply(live, config, "v1", managers, "A", false)
		if err != nil {
			t.Fatal(err)
		}
		if obj == nil {
			continue // no change
		}
		if _, ok := obj.AsValue().Unstructured().(map[string]interface{})["spec"]; !ok {
			t.Errorf("live spec %v: re-applying spec: {} deleted spec: %v", spec, obj.AsValue().Unstructured())
		}
	}
}
