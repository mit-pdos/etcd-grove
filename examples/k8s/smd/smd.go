// Package smd is a top-level driver for Kubernetes' structured-merge-diff (SMD) v7.0.0, the
// library the API server's server-side apply uses: Main runs a scenario of several field
// managers applying (merge.Updater.Apply) and updating (merge.Updater.Update) one object, and
// panics unless every result (the object, each manager's owned field set, the conflicts) is the
// one written out here by hand. A robustness proof of Main is a proof that SMD computes exactly
// these results.
//
// To keep the verified surface small, the scenario stays on SMD's unstructured values
// (value.NewValueInterface of map[string]interface{}, []interface{}, string and int64): it never
// builds a reflection-backed value, never parses a schema (the schema is a Go literal, not YAML),
// never serializes a field set, and its converter is the identity.
package smd

import (
	"sigs.k8s.io/structured-merge-diff/v7/fieldpath"
	"sigs.k8s.io/structured-merge-diff/v7/merge"
	"sigs.k8s.io/structured-merge-diff/v7/schema"
	"sigs.k8s.io/structured-merge-diff/v7/typed"
	"sigs.k8s.io/structured-merge-diff/v7/value"
)

// version is the one API version of the scenario.
const version = fieldpath.APIVersion("v1")

// identityConverter is a converter for a single API version: converting is the identity, and
// no version is ever missing.
type identityConverter struct{}

func (identityConverter) Convert(object *typed.TypedValue, _ fieldpath.APIVersion) (*typed.TypedValue, error) {
	return object, nil
}

func (identityConverter) IsMissingVersionError(_ error) bool {
	return false
}

// newSchema is the scenario's schema, type "root":
//
//	root:      name, image: string; replicas: numeric;
//	           containers: list of container, associative, key name (granular);
//	           labels:     map of string (granular);
//	           selector:   map of string, atomic
//	container: name, image: string; port: numeric
func newSchema() *schema.Schema {
	stringName := "string"
	numericName := "numeric"
	containerName := "container"
	labelsName := "labels"
	selectorName := "selector"
	containersName := "containers"
	str := schema.String
	num := schema.Numeric
	strRef := schema.TypeRef{NamedType: &stringName}
	numRef := schema.TypeRef{NamedType: &numericName}
	return &schema.Schema{Types: []schema.TypeDef{
		{Name: "root", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "name", Type: strRef},
			{Name: "image", Type: strRef},
			{Name: "replicas", Type: numRef},
			{Name: "containers", Type: schema.TypeRef{NamedType: &containersName}},
			{Name: "labels", Type: schema.TypeRef{NamedType: &labelsName}},
			{Name: "selector", Type: schema.TypeRef{NamedType: &selectorName}},
		}}}},
		{Name: "container", Atom: schema.Atom{Map: &schema.Map{Fields: []schema.StructField{
			{Name: "name", Type: strRef},
			{Name: "image", Type: strRef},
			{Name: "port", Type: numRef},
		}}}},
		{Name: "containers", Atom: schema.Atom{List: &schema.List{
			ElementType:         schema.TypeRef{NamedType: &containerName},
			ElementRelationship: schema.Associative,
			Keys:                []string{"name"},
		}}},
		{Name: "labels", Atom: schema.Atom{Map: &schema.Map{
			ElementType:         strRef,
			ElementRelationship: schema.Separable,
		}}},
		{Name: "selector", Atom: schema.Atom{Map: &schema.Map{
			ElementType:         strRef,
			ElementRelationship: schema.Atomic,
		}}},
		{Name: "string", Atom: schema.Atom{Scalar: &str}},
		{Name: "numeric", Atom: schema.Atom{Scalar: &num}},
	}}
}

// state is the object as stored, and its managed fields.
type state struct {
	sc       *schema.Schema
	updater  *merge.Updater
	live     *typed.TypedValue
	managers fieldpath.ManagedFields
}

// typedObj types an unstructured object as a root, panicking if it does not validate.
func (s *state) typedObj(obj map[string]interface{}) *typed.TypedValue {
	rootName := "root"
	tv, err := typed.AsTyped(value.NewValueInterface(obj), s.sc, schema.TypeRef{NamedType: &rootName})
	if err != nil {
		panic("smd: scenario object does not validate")
	}
	return tv
}

// apply applies config as manager, without force, and stores the result; it panics on an error.
// It returns whether the object changed: Apply returns a nil object when it did not (the updater
// is built as the API server builds it, without ReturnInputOnNoop), and the API server then keeps
// the live object.
func (s *state) apply(config map[string]interface{}, manager string, msg string) bool {
	obj, managers, err := s.updater.Apply(s.live, s.typedObj(config), version, s.managers, manager, false)
	if err != nil {
		panic(msg)
	}
	s.managers = managers
	if obj == nil {
		return false
	}
	s.live = obj
	return true
}

// check panics with msg unless the stored object is obj and the managed fields are managers.
func (s *state) check(obj map[string]interface{}, managers fieldpath.ManagedFields, msg string) {
	if !value.Equals(s.live.AsValue(), value.NewValueInterface(obj)) {
		panic(msg)
	}
	if !s.managers.Equals(managers) {
		panic(msg)
	}
}

// Paths. A field of the root, a key of a map field, a list item by its key, a field of a list item.

func field(name string) fieldpath.Path {
	return fieldpath.Path{fieldpath.FieldNameElement(name)}
}

func mapKey(name string, key string) fieldpath.Path {
	return fieldpath.Path{fieldpath.FieldNameElement(name), fieldpath.FieldNameElement(key)}
}

func item(key string) fieldpath.Path {
	return fieldpath.Path{fieldpath.FieldNameElement("containers"),
		fieldpath.KeyElement(value.Field{Name: "name", Value: value.NewValueInterface(key)})}
}

func itemField(key string, name string) fieldpath.Path {
	return fieldpath.Path{fieldpath.FieldNameElement("containers"),
		fieldpath.KeyElement(value.Field{Name: "name", Value: value.NewValueInterface(key)}),
		fieldpath.FieldNameElement(name)}
}

// The paths a container's apply owns: the item, its key and its image.
func containerPaths(key string) []fieldpath.Path {
	return []fieldpath.Path{item(key), itemField(key, "name"), itemField(key, "image")}
}

func applied(paths ...fieldpath.Path) fieldpath.VersionedSet {
	return fieldpath.NewVersionedSet(fieldpath.NewSet(paths...), version, true)
}

func updated(paths ...fieldpath.Path) fieldpath.VersionedSet {
	return fieldpath.NewVersionedSet(fieldpath.NewSet(paths...), version, false)
}

func container(name string, image string) map[string]interface{} {
	return map[string]interface{}{"name": name, "image": image}
}

func concat(a []fieldpath.Path, b []fieldpath.Path) []fieldpath.Path {
	return append(append([]fieldpath.Path{}, a...), b...)
}

// Main runs the scenario. Managers A and B apply, C updates.
func Main() {
	s := &state{
		sc:       newSchema(),
		updater:  (&merge.UpdaterBuilder{Converter: identityConverter{}}).BuildUpdater(),
		managers: fieldpath.ManagedFields{},
	}
	s.live = s.typedObj(map[string]interface{}{})

	// 1. A creates the object by Apply; A owns exactly what it applied (the atomic selector as
	// one field).
	s.apply(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(1),
		"containers": []interface{}{container("a1", "x")},
		"labels":     map[string]interface{}{"app": "web"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, "A", "smd: 1: apply by A failed")
	aPaths1 := concat([]fieldpath.Path{field("name"), field("image"), field("replicas"),
		mapKey("labels", "app"), field("selector")}, containerPaths("a1"))
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(1),
		"containers": []interface{}{container("a1", "x")},
		"labels":     map[string]interface{}{"app": "web"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{"A": applied(aPaths1...)}, "smd: 1: wrong object or ownership after A's create")

	// 2. B applies a disjoint field: merged object, both ownerships exact.
	s.apply(map[string]interface{}{
		"labels": map[string]interface{}{"team": "t"},
	}, "B", "smd: 2: apply by B failed")
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(1),
		"containers": []interface{}{container("a1", "x")},
		"labels":     map[string]interface{}{"app": "web", "team": "t"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths1...),
		"B": applied(mapKey("labels", "team")),
	}, "smd: 2: wrong object or ownership after B's disjoint apply")

	// 3. B applies the value A has for image: no conflict, both own it, object unchanged (Apply
	// reports the no-op).
	if s.apply(map[string]interface{}{
		"image":  "img1",
		"labels": map[string]interface{}{"team": "t"},
	}, "B", "smd: 3: apply of an equal value conflicted") {
		panic("smd: 3: apply of an equal value changed the object")
	}
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(1),
		"containers": []interface{}{container("a1", "x")},
		"labels":     map[string]interface{}{"app": "web", "team": "t"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths1...),
		"B": applied(field("image"), mapKey("labels", "team")),
	}, "smd: 3: wrong object or ownership after B's co-owning apply")

	// 4. B applies a different value for replicas, which A owns, without force: a conflict with A
	// on replicas and nothing else; the stored object and managed fields are not changed.
	config4 := map[string]interface{}{
		"image":    "img1",
		"replicas": int64(2),
		"labels":   map[string]interface{}{"team": "t"},
	}
	_, _, err := s.updater.Apply(s.live, s.typedObj(config4), version, s.managers, "B", false)
	if err == nil {
		panic("smd: 4: conflicting apply succeeded")
	}
	conflicts, ok := err.(merge.Conflicts)
	if !ok {
		panic("smd: 4: conflicting apply failed with an error that is not a conflict")
	}
	if !conflicts.Equals(merge.Conflicts{merge.Conflict{Manager: "A", Path: field("replicas")}}) {
		panic("smd: 4: wrong conflicts")
	}
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(1),
		"containers": []interface{}{container("a1", "x")},
		"labels":     map[string]interface{}{"app": "web", "team": "t"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths1...),
		"B": applied(field("image"), mapKey("labels", "team")),
	}, "smd: 4: a conflicting apply changed the object or the managed fields")

	// 5. The same apply with force: the value changes, B owns replicas, A loses it.
	obj5, managers5, err := s.updater.Apply(s.live, s.typedObj(config4), version, s.managers, "B", true)
	if err != nil {
		panic("smd: 5: forced apply failed")
	}
	s.live = obj5
	s.managers = managers5
	aPaths5 := concat([]fieldpath.Path{field("name"), field("image"),
		mapKey("labels", "app"), field("selector")}, containerPaths("a1"))
	bPaths5 := []fieldpath.Path{field("image"), field("replicas"), mapKey("labels", "team")}
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(2),
		"containers": []interface{}{container("a1", "x")},
		"labels":     map[string]interface{}{"app": "web", "team": "t"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths5...),
		"B": applied(bPaths5...),
	}, "smd: 5: wrong object or ownership after B's forced apply")

	// 6. A applies again omitting labels.app, which it alone owns (pruned), and image, which B
	// also owns (kept).
	s.apply(map[string]interface{}{
		"name":       "obj",
		"containers": []interface{}{container("a1", "x")},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, "A", "smd: 6: apply by A failed")
	aPaths6 := concat([]fieldpath.Path{field("name"), field("selector")}, containerPaths("a1"))
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(2),
		"containers": []interface{}{container("a1", "x")},
		"labels":     map[string]interface{}{"team": "t"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths6...),
		"B": applied(bPaths5...),
	}, "smd: 6: wrong object or ownership after A's apply omitting fields")

	// 7. B adds a list item with another key: it coexists with A's. Then A replaces its item a1
	// by a2: only a1 is removed.
	s.apply(map[string]interface{}{
		"image":      "img1",
		"replicas":   int64(2),
		"containers": []interface{}{container("b1", "y")},
		"labels":     map[string]interface{}{"team": "t"},
	}, "B", "smd: 7: apply by B of a list item failed")
	bPaths7 := concat(bPaths5, containerPaths("b1"))
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(2),
		"containers": []interface{}{container("a1", "x"), container("b1", "y")},
		"labels":     map[string]interface{}{"team": "t"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths6...),
		"B": applied(bPaths7...),
	}, "smd: 7: wrong object or ownership after B's list item")
	s.apply(map[string]interface{}{
		"name":       "obj",
		"containers": []interface{}{container("a2", "z")},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, "A", "smd: 7: apply by A replacing its list item failed")
	aPaths7 := concat([]fieldpath.Path{field("name"), field("selector")}, containerPaths("a2"))
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(2),
		"containers": []interface{}{container("b1", "y"), container("a2", "z")},
		"labels":     map[string]interface{}{"team": "t"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths7...),
		"B": applied(bPaths7...),
	}, "smd: 7: wrong object or ownership after A's list item replacement")

	// 8. C updates replicas (B's) and adds labels.env: C owns exactly those two, B loses replicas
	// and keeps the rest, A is untouched.
	obj8, managers8, err := s.updater.Update(s.live, s.typedObj(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(3),
		"containers": []interface{}{container("b1", "y"), container("a2", "z")},
		"labels":     map[string]interface{}{"team": "t", "env": "prod"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}), version, s.managers, "C")
	if err != nil {
		panic("smd: 8: update by C failed")
	}
	s.live = obj8
	s.managers = managers8
	bPaths8 := concat([]fieldpath.Path{field("image"), mapKey("labels", "team")}, containerPaths("b1"))
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(3),
		"containers": []interface{}{container("b1", "y"), container("a2", "z")},
		"labels":     map[string]interface{}{"team": "t", "env": "prod"},
		"selector":   map[string]interface{}{"k": "v1", "m": "x"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths7...),
		"B": applied(bPaths8...),
		"C": updated(field("replicas"), mapKey("labels", "env")),
	}, "smd: 8: wrong object or ownership after C's update")

	// 9. A applies a changed atomic selector: it is replaced whole (m is gone), and A owns the
	// selector as one field, none of its keys.
	s.apply(map[string]interface{}{
		"name":       "obj",
		"containers": []interface{}{container("a2", "z")},
		"selector":   map[string]interface{}{"k": "v2"},
	}, "A", "smd: 9: apply by A of a changed atomic field failed")
	s.check(map[string]interface{}{
		"name":       "obj",
		"image":      "img1",
		"replicas":   int64(3),
		"containers": []interface{}{container("b1", "y"), container("a2", "z")},
		"labels":     map[string]interface{}{"team": "t", "env": "prod"},
		"selector":   map[string]interface{}{"k": "v2"},
	}, fieldpath.ManagedFields{
		"A": applied(aPaths7...),
		"B": applied(bPaths8...),
		"C": updated(field("replicas"), mapKey("labels", "env")),
	}, "smd: 9: wrong object or ownership after A's atomic change")
}
