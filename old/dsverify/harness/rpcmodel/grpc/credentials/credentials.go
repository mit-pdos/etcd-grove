// Package credentials is the dsverify lab's model of google.golang.org/grpc/credentials
// (v1.84.0): only the type of transport credentials, of which the model knows one, insecure's.
package credentials

// TransportCredentials defines the common interface for all transport credentials (the model's
// has no methods: insecure.NewCredentials() is its only value a program can make).
type TransportCredentials interface{}
