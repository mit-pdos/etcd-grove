package reflect

// Slice operations at a run-time type: how the apiserver fills a list
// object's Items slice, whose element type it knows only by reflection.
//
// Mirrors k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038/pkg/storage/:
//   - etcd3/store.go:780-782 (GetList: `listPtr, err := meta.GetItemsPtr(listObj)`,
//     `v, err := conversion.EnforcePtr(listPtr)`, `if err != nil || v.Kind() != reflect.Slice`);
//   - etcd3/store.go:1117-1140 (growSlice: Cap, Len, `reflect.MakeSlice(v.Type(), v.Len(), max)`,
//     `reflect.Copy(extra, v)`, `v.Set(extra)`);
//   - etcd3/store.go:1048 (processListItem: `v.Set(reflect.Append(v, reflect.ValueOf(obj).Elem()))`);
//   - etcd3/store.go:1010-1012 (finalizeList: `if v.IsNil() { v.Set(reflect.MakeSlice(v.Type(), 0, 0)) }`);
//   - cacher/cacher.go:823-828, 866-872 (`listVal.Set(reflect.MakeSlice(listVal.Type(), n, n))`,
//     `listVal.Index(i).Set(reflect.ValueOf(o).Elem())`);
// and k8s.io/apimachinery@v0.0.0-20261021173754-0b7d352f711c/pkg/api/meta/
// help.go:89-110 (getItemsPtr: EnforcePtr, `items := v.FieldByName("Items")`,
// IsValid, Kind Interface/Pointer or `items.Addr().Interface()`).
// The etcd3 functions are translated with their bodies
// (Code/k8s_io/apiserver/pkg/storage/etcd3.lean: GetList, growSlice,
// processListItem, finalizeList, appendChunk); getItemsPtr is names-only.
//
// Go's panics: Append of a value whose type is not the slice's element type
// panics "reflect.Set: value of type *reflect.Pod2 is not assignable to type
// reflect.Pod2"; Index out of range "reflect: slice index out of range";
// MakeSlice of a non-slice type "reflect.MakeSlice of non-slice type".
//
// To prove: the store's sequence keeps the list object's Items equal to the
// matched objects in order (Append), keeps them through growSlice (Copy and
// Set preserve the elements, the capacity grows), and leaves Items non-nil
// and empty when nothing matched (finalizeList). The panics are excluded by
// the element type: each appended value is ValueOf(newItemFunc()).Elem(),
// whose type is v.Type().Elem() (ptrset.go).
//
// Needs R1 (Elem of a slice type, FieldByName on a struct type) and R2
// (FieldByName, IsValid, Addr, Interface, Kind, Len, Cap, IsNil, MakeSlice,
// Copy, Append, Index, Set: a Value aliasing a struct field of the caller's
// object).

import "reflect"

type PodList struct {
	ResourceVersion string
	Items           []Pod2
}

// getItemsPtr is meta.getItemsPtr (help.go:89-110), its errors as strings.
func getItemsPtr(list any) (any, string) {
	v, err := enforcePtr(list)
	if err != "" {
		return nil, err
	}
	items := v.FieldByName("Items")
	if !items.IsValid() {
		return nil, "no Items field in this object"
	}
	switch items.Kind() {
	case reflect.Interface, reflect.Pointer:
		target := reflect.TypeOf(items.Interface()).Elem()
		if target.Kind() != reflect.Slice {
			return nil, "Items field must be a slice of objects"
		}
		return items.Interface(), ""
	case reflect.Slice:
		return items.Addr().Interface(), ""
	default:
		return nil, "Items field must be a slice of objects"
	}
}

// growSlice is store.go:1117.
func growSlice(v reflect.Value, maxCapacity int, sizes ...int) {
	cap := v.Cap()
	max := cap
	for _, size := range sizes {
		if size > max {
			max = size
		}
	}
	if len(sizes) == 0 || max > maxCapacity {
		max = maxCapacity
	}
	if max <= cap {
		return
	}
	if v.Len() > 0 {
		extra := reflect.MakeSlice(v.Type(), v.Len(), max)
		reflect.Copy(extra, v)
		v.Set(extra)
	} else {
		extra := reflect.MakeSlice(v.Type(), 0, max)
		v.Set(extra)
	}
}

// getList is the reflective skeleton of store.GetList: Items through
// getItemsPtr and EnforcePtr, grown, one Append per matched object, and
// finalizeList's non-nil Items.
func getList(listObj any, names []string, match func(string) bool) string {
	listPtr, err := getItemsPtr(listObj)
	if err != "" {
		return err
	}
	v, err := enforcePtr(listPtr)
	if err != "" || v.Kind() != reflect.Slice {
		return "need ptr to slice: " + err
	}
	elem := v.Type().Elem()
	growSlice(v, 2048, len(names))
	for _, n := range names {
		obj := reflect.New(elem).Interface().(Object)
		obj.(*Pod2).Name = n // the decode of the stored object
		if match(n) {
			v.Set(reflect.Append(v, reflect.ValueOf(obj).Elem()))
		}
	}
	if v.IsNil() {
		v.Set(reflect.MakeSlice(v.Type(), 0, 0))
	}
	return ""
}

// fillFromCache is cacher.go:866-872: a slice of the cached objects' copies.
func fillFromCache(listVal reflect.Value, objs []Object) {
	listVal.Set(reflect.MakeSlice(listVal.Type(), len(objs), len(objs)))
	for i, o := range objs {
		listVal.Index(i).Set(reflect.ValueOf(o).Elem())
	}
}

// REQ reflect/list-items: the store's reflective list filling leaves Items equal to the
// matched objects, in order, non-nil when none matched, and through growSlice keeps the
// elements already there; the cacher's fill copies each object into its slot; getItemsPtr
// refuses an object with no Items field.
// Users: apiserver storage/etcd3/store.go:780-782,1010-1012,1048,1117-1140 (translated);
// storage/cacher/cacher.go:823-828,866-872; apimachinery api/meta/help.go:89-110.
// Assumes: nothing.
// Specs: none yet; needs R1 (Elem, FieldByName) and R2 (MakeSlice, Copy, Append, Index, Set,
// Len, Cap, IsNil, Addr) (doc.go).
func ReqListItems() {
	list := &PodList{}
	if err := getList(list, []string{"a", "b", "c"}, func(n string) bool { return n != "b" }); err != "" {
		panic("list-items: " + err)
	}
	if len(list.Items) != 2 || list.Items[0].Name != "a" || list.Items[1].Name != "c" {
		panic("list-items: Items are the matched objects in order")
	}
	empty := &PodList{}
	if err := getList(empty, []string{"a"}, func(string) bool { return false }); err != "" || empty.Items == nil || len(empty.Items) != 0 {
		panic("list-items: no match leaves Items empty, not nil")
	}
	pre := &PodList{Items: make([]Pod2, 1, 1)}
	pre.Items[0].Name = "kept"
	growSlice(reflect.ValueOf(&pre.Items).Elem(), 10, 5)
	if len(pre.Items) != 1 || cap(pre.Items) != 5 || pre.Items[0].Name != "kept" {
		panic("list-items: growSlice keeps the elements")
	}
	cachedList := &PodList{}
	fillFromCache(reflect.ValueOf(&cachedList.Items).Elem(), []Object{&Pod2{Name: "x"}, &Pod2{Name: "y"}})
	if len(cachedList.Items) != 2 || cachedList.Items[1].Name != "y" {
		panic("list-items: the cacher's fill")
	}
	if _, err := getItemsPtr(&Pod2{}); err != "no Items field in this object" {
		panic("list-items: an object with no Items")
	}
}

// REQ reflect/list-items (panics): Append of a *Pod2 to a []Pod2 panics "reflect.Set: value of
// type *reflect.Pod2 is not assignable to type reflect.Pod2" (processListItem with the Elem
// forgotten).
// Specs: none yet.
func MustPanicAppendWrongElem() {
	v := reflect.ValueOf(&[]Pod2{}).Elem()
	v.Set(reflect.Append(v, reflect.ValueOf(&Pod2{})))
}
