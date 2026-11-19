package merge_test

import (
	"testing"

	"sigs.k8s.io/structured-merge-diff/v7/fieldpath"
	"sigs.k8s.io/structured-merge-diff/v7/merge"
	"sigs.k8s.io/structured-merge-diff/v7/schema"
	"sigs.k8s.io/structured-merge-diff/v7/typed"
	"sigs.k8s.io/structured-merge-diff/v7/value"
)

type ifIdentityConverter struct{}

func (ifIdentityConverter) Convert(o *typed.TypedValue, _ fieldpath.APIVersion) (*typed.TypedValue, error) {
	return o, nil
}
func (ifIdentityConverter) IsMissingVersionError(error) bool { return false }

// TestIgnoredFieldsOtherVersion: an updater built with fields to ignore at version v1 is used for
// a request at version v2. Apply and Update panic (nil pointer dereference) instead of ignoring
// nothing at v2.
func TestIgnoredFieldsOtherVersion(t *testing.T) {
	s := schema.String
	ref := func(name string) schema.TypeRef { return schema.TypeRef{NamedType: &name} }
	sc := &schema.Schema{Types: []schema.TypeDef{
		{Name: "root", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "name", Type: ref("string")},
			{Name: "status", Type: ref("string")},
		}}}},
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
	updater := (&merge.UpdaterBuilder{
		Converter:     ifIdentityConverter{},
		IgnoredFields: map[fieldpath.APIVersion]*fieldpath.Set{"v1": fieldpath.NewSet(fieldpath.MakePathOrDie("status"))},
	}).BuildUpdater()
	live := typed(map[string]interface{}{"name": "o"})
	config := typed(map[string]interface{}{"name": "p"})
	run := func(what string, f func() error) {
		defer func() {
			if r := recover(); r != nil {
				t.Errorf("%s at v2 panicked: %v", what, r)
			}
		}()
		if err := f(); err != nil {
			t.Errorf("%s at v2: %v", what, err)
		}
	}
	run("Apply", func() error {
		_, _, err := updater.Apply(live, config, "v2", fieldpath.ManagedFields{}, "A", false)
		return err
	})
	run("Update", func() error {
		_, _, err := updater.Update(live, config, "v2", fieldpath.ManagedFields{}, "A")
		return err
	})
}
