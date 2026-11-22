package robust

import (
	"fmt"
	"io"
	"os"
	"os/exec"
	"strings"
)

// IsRoot says whether this process runs as root.
func IsRoot() bool { return os.Geteuid() == 0 }

// run runs a command; its error carries the command's output.
func run(args ...string) (string, error) {
	return runIn("", args...)
}

// runIn runs a command with stdin.
func runIn(stdin string, args ...string) (string, error) {
	cmd := exec.Command(args[0], args[1:]...)
	if stdin != "" {
		cmd.Stdin = strings.NewReader(stdin)
	}
	out, err := cmd.CombinedOutput()
	if err != nil {
		return "", fmt.Errorf("%s: %v: %s", strings.Join(args, " "), err, strings.TrimSpace(string(out)))
	}
	return strings.TrimSpace(string(out)), nil
}

// asRoot runs a command as root: directly if this process is root, by sudo -n otherwise.
func asRoot(args ...string) (string, error) {
	if !IsRoot() {
		args = append([]string{"sudo", "-n"}, args...)
	}
	return run(args...)
}

// asRootIn is asRoot with stdin.
func asRootIn(stdin string, args ...string) error {
	if !IsRoot() {
		args = append([]string{"sudo", "-n"}, args...)
	}
	_, err := runIn(stdin, args...)
	return err
}

// RerunAsRoot runs this program's binary again, as root (sudo -n), with the arguments args (the
// binary's own name excluded) and the environment variables env added, its output to out, and
// returns how it exited. The way a test or a command that needs network namespaces gets root
// without the rest of its work being privileged.
func RerunAsRoot(args, env []string, out io.Writer) error {
	exe, err := os.Executable()
	if err != nil {
		return err
	}
	cmd := exec.Command("sudo", append(append(append([]string{"-n", "env"}, env...), exe), args...)...)
	cmd.Stdout, cmd.Stderr = out, out
	return cmd.Run()
}

// RerunInUserns runs this program's binary again inside a user namespace of its own, with a
// network and a mount namespace (unshare -Urnm), where it is root with every capability over its
// own namespaces: the way a process that is root without CAP_NET_ADMIN (a container's root) makes
// network namespaces (NewNetwork, the bridge variant). The arguments args (the binary's name
// excluded) and the environment variables env are added; /run/netns is a fresh tmpfs inside, so
// that its namespaces are invisible to the host's ip netns. Disks (power losses) are not
// available there: the device mapper needs the host's root.
func RerunInUserns(args, env []string, out io.Writer) error {
	exe, err := os.Executable()
	if err != nil {
		return err
	}
	script := "mkdir -p /run/netns && mount -t tmpfs robust-netns /run/netns && exec \"$0\" \"$@\""
	cmd := exec.Command("unshare", append([]string{"-Urnm", "--propagation", "private", "sh", "-c",
		script, exe}, args...)...)
	cmd.Env = append(os.Environ(), env...)
	cmd.Stdout, cmd.Stderr = out, out
	return cmd.Run()
}
