Title: Adding a user or role with a name longer than 32768 bytes makes every member exit

### What happened?

In a three-member cluster with the default configuration, `etcdctl role add` with a 32768-byte name succeeds, and with a 32769-byte name every member exits:

```console
$ etcdctl role add "$(printf "a%.0s" $(seq 32768))"
Role aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa... created
$ etcdctl role add "$(printf "a%.0s" $(seq 32769))"
Error: rpc error: code = Unavailable desc = error reading from server: EOF
$ etcdctl endpoint health
http://127.0.0.1:23791 is unhealthy: failed to commit proposal: context deadline exceeded
http://127.0.0.1:23792 is unhealthy: failed to commit proposal: context deadline exceeded
http://127.0.0.1:23793 is unhealthy: failed to commit proposal: context deadline exceeded
```

Each of the three members logs, then exits:

```
{"level":"fatal","caller":"backend/batch_tx.go:184","msg":"failed to write to a bucket","bucket-name":"authRoles","error":"key too large",...}
```

After restarting all three members, every member logs the same line and exits again, so the cluster stays down. `etcdctl user add` with a 32769-byte name does the same (`"bucket-name":"authUsers"`). This affects any cluster where a client allowed to add users or roles (any client while auth is disabled) sends such a name.

### What did you expect to happen?

Adding a user or role whose name is too long should fail with an error, as an empty name does, and the members should keep running.

### How can we reproduce it (as minimally and precisely as possible)?

Start a three-member cluster built from `main` (3aaab3479) with the default configuration and run the `etcdctl` commands above.

Test: [`TestRoleAdd_Error`](https://github.com/upamanyus/etcd/blob/fix/etcd-auth-useradd-long-name-fatal/tests/common/role_test.go#L49-L66) and the case `username_longer_than_max_key_size_not_allowed` of [`TestUserAdd_Simple`](https://github.com/upamanyus/etcd/blob/fix/etcd-auth-useradd-long-name-fatal/tests/common/user_test.go#L30-L94), on branch [`upamanyus/etcd:fix/etcd-auth-useradd-long-name-fatal`](https://github.com/upamanyus/etcd/tree/fix/etcd-auth-useradd-long-name-fatal), off `main` (3aaab3479). On `main`, `cd tests && go test -tags integration ./common/ -run 'TestRoleAdd_Error$' -v` stops the test binary (output trimmed):

```
    logger.go:146: 2026-10-23T14:59:13.069Z	FATAL	m0	failed to write to a bucket	{"member": "m0", "bucket-name": "authRoles", "error": "key too large"}
FAIL	go.etcd.io/etcd/tests/v3/common	0.263s
```

### Anything else we need to know?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

```console
$ etcd --version
etcd Version: 3.8.0-alpha.0
Git SHA: 3aaab3479
Go Version: go1.27.3
Go OS/Arch: linux/amd64

$ etcdctl version
etcdctl version: 3.8.0-alpha.0
API version: 3.8
```

</details>

### Etcd configuration (command line flags or environment variables)

<details>

Defaults (auth disabled), three members on localhost.

</details>
