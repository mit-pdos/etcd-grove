package merge_test

import (
	"testing"

	"sigs.k8s.io/structured-merge-diff/v7/fieldpath"
	"sigs.k8s.io/structured-merge-diff/v7/merge"
	"sigs.k8s.io/structured-merge-diff/v7/schema"
	"sigs.k8s.io/structured-merge-diff/v7/typed"
	"sigs.k8s.io/structured-merge-diff/v7/value"
)

type mvIdentityConverter struct{}

func (mvIdentityConverter) Convert(o *typed.TypedValue, _ fieldpath.APIVersion) (*typed.TypedValue, error) {
	return o, nil
}
func (mvIdentityConverter) IsMissingVersionError(error) bool { return false }

func mvSchema() *schema.Schema {
	s, n := schema.String, schema.Numeric
	ref := func(name string) schema.TypeRef { return schema.TypeRef{NamedType: &name} }
	return &schema.Schema{Types: []schema.TypeDef{
		{Name: "root", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "name", Type: ref("string")},
			{Name: "image", Type: ref("string")},
			{Name: "containers", Type: ref("containers")},
		}}}},
		{Name: "container", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "name", Type: ref("string")},
			{Name: "port", Type: ref("numeric")},
		}}}},
		{Name: "containers", Atom: schema.Atom{List: &schema.List{
			ElementType: ref("container"), ElementRelationship: schema.Associative, Keys: []string{"name"}}}},
		{Name: "string", Atom: schema.Atom{Scalar: &s}},
		{Name: "numeric", Atom: schema.Atom{Scalar: &n}},
	}}
}

// TestApplyMultiVersionPrunesOwnedField: manager B applies at v1 and gives up the field
// containers[name=b].port, which manager C, also at v1, still owns. The field must stay. It does
// when the unrelated manager A (which owns only the item containers[name=b] and its key) is at
// v1; when A is at v2, Apply removes the field C owns.
func TestApplyMultiVersionPrunesOwnedField(t *testing.T) {
	sc := mvSchema()
	rootName := "root"
	typed := func(o map[string]interface{}) *typed.TypedValue {
		tv, err := typed.AsTyped(value.NewValueInterface(o), sc, schema.TypeRef{NamedType: &rootName})
		if err != nil {
			t.Fatal(err)
		}
		return tv
	}
	live := map[string]interface{}{"image": "c", "containers": []interface{}{
		map[string]interface{}{"name": "b", "port": int64(1)}, map[string]interface{}{"name": "c"}}}
	kb, kc := fieldpath.KeyByFields("name", "b"), fieldpath.KeyByFields("name", "c")
	others := func() *fieldpath.Set {
		return fieldpath.NewSet(fieldpath.MakePathOrDie("containers", kb, "port"),
			fieldpath.MakePathOrDie("containers", kc), fieldpath.MakePathOrDie("containers", kc, "name"),
			fieldpath.MakePathOrDie("image"))
	}
	for _, versionA := range []fieldpath.APIVersion{"v1", "v2"} {
		managers := fieldpath.ManagedFields{
			"A": fieldpath.NewVersionedSet(fieldpath.NewSet(fieldpath.MakePathOrDie("containers", kb),
				fieldpath.MakePathOrDie("containers", kb, "name")), versionA, true),
			"B": fieldpath.NewVersionedSet(others(), "v1", true),
			"C": fieldpath.NewVersionedSet(others(), "v1", true),
		}
		updater := (&merge.UpdaterBuilder{Converter: mvIdentityConverter{}}).BuildUpdater()
		obj, _, err := updater.Apply(typed(live), typed(map[string]interface{}{"name": "x"}), "v1", managers, "B", false)
		if err != nil {
			t.Fatalf("A at %s: %v", versionA, err)
		}
		containers := obj.AsValue().Unstructured().(map[string]interface{})["containers"].([]interface{})
		if _, ok := containers[0].(map[string]interface{})["port"]; !ok {
			t.Errorf("A at %s: containers[name=b].port, owned by C at v1, was removed: %v", versionA, containers)
		}
	}
}
