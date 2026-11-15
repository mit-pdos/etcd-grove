package semantics

// fill returns n copies of the byte b.
func fill(n int, b byte) []byte {
	p := make([]byte, n)
	for i := range p {
		p[i] = b
	}
	return p
}
