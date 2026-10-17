// What a v3.7 member does with an X-Server-Version header: rafthttp's serverVersion
// (release-3.7, server/etcdserver/api/rafthttp/util.go) is
// semver.Must(semver.NewVersion(verStr)) of github.com/coreos/go-semver.
package main

import (
	"fmt"

	"github.com/coreos/go-semver/semver"
)

func main() {
	for _, s := range []string{"3.8.0", "v3.8.0"} {
		_, err := semver.NewVersion(s)
		fmt.Printf("NewVersion(%q): err = %v\n", s, err)
	}
	defer func() { fmt.Printf("Must(NewVersion(\"v3.8.0\")) panics: %v\n", recover()) }()
	semver.Must(semver.NewVersion("v3.8.0"))
}
