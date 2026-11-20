package reflect

import "testing"

// TestSnippets runs every snippet: each panics if what its users rely on fails.
func TestSnippets(t *testing.T) {
	ReqStructTags()
	ReqRegisterService()
	ReqHTTPUnwrap()
	ReqErrorsAs()
}
