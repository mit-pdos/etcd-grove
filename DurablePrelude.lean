/-
The prelude for code that uses the durable-state extension
(`github.com/mit-pdos/etcd-grove/examples/durable`): its definition, `durableExt`. The code
assumes `[ElemExt durableExt]`. Goose imports it by name: the code prelude of the extension
`durable` (`-ext github.com/mit-pdos/etcd-grove/examples/durable=durable`, `etc/goose.py`),
whose package has the empty Lean root.
-/
module

public import GooseLang.Ext.Durable.Impl
