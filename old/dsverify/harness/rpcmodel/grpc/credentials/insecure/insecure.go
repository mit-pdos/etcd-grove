// Package insecure is the dsverify lab's model of google.golang.org/grpc/credentials/insecure
// (v1.84.0): credentials that disable transport security (plain TCP, as the model's transport).
package insecure

import "google.golang.org/grpc/credentials"

// insecureTC is the type of the insecure credentials.
type insecureTC struct{}

// NewCredentials returns credentials which disable transport security.
func NewCredentials() credentials.TransportCredentials {
	return insecureTC{}
}
