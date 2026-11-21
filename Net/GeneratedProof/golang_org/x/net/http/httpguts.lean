/-
Hand-written, not generated: goose imports a vendored standard-library package by its import path
(`golang.org/x/net/http/httpguts`, this module) but translates it, and names its declarations, by
its package path (`vendor/golang.org/x/net/http/httpguts`: `Net.GeneratedProof.vendor.golang_org.x.net.http.
httpguts`, namespace `Perennial.vendor.golang_org.x.net.http.httpguts`). This module forwards the
import (`notes/perennial-changes.md`, 2026-11-20, "goose imports a vendored package by its import
path"). Project models-net's lean root `golang.org/x/net/http/httpguts=Net` (`etc/goose.py`).
-/
module

public import Net.GeneratedProof.vendor.golang_org.x.net.http.httpguts
