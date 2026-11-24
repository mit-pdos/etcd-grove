package rpcdifftest

// Deep exercises gob's merging (decoding into a non-zero reply): nested structs, pointer fields,
// slices of structs, maps of structs, named basic types, a byte slice, an unexported field (gob
// ignores it).
type Deep struct {
	Name   Label
	Inner  Args
	Ptr    *Args
	PStr   *string
	Items  []Item
	ByKey  map[string]Item
	Raw    []byte
	Flag   bool
	Small  int8
	hidden uint64
}

// Label is a named string.
type Label string

// Item is a slice element.
type Item struct {
	K string
	V int64
	W []uint16
}

// Swap returns its argument with Inner's fields swapped, and a copy of them through Ptr.
func (t *Arith) Swap(a *Deep, r *Deep) error {
	*r = *a
	r.Inner = Args{A: a.Inner.B, B: a.Inner.A}
	c := r.Inner
	r.Ptr = &c
	r.hidden = 7
	return nil
}

// List returns a slice reply (made empty by the server before the call).
func (t *Arith) List(n int, r *[]Item) error {
	for i := 0; i < n; i++ {
		*r = append(*r, Item{K: "k", V: int64(i)})
	}
	return nil
}

// Value takes its argument by value.
func (t *Arith) Value(a Args, r *Reply) error {
	r.C = a.A * a.B
	return nil
}

// Hidden is a method net/rpc does not register (unexported).
func (t *Arith) hidden(a *Args, r *Reply) error { return nil }

var _ = (*Arith).hidden
