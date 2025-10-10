# Haskelite-coq

Proving Haskelite's big-step and small-step semantics equivalent.

## Building

Run the following command:

```bash
dune build
```

Or, if you have Nix:

```bash
nix build
```

## Devshell

To enter a devshell with all dependencies and development tools needed for the project:

```bash
nix develop .# -c $SHELL
```
