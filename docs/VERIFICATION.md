# Verification

## Local verification

Run:

```sh
./scripts/verify.sh
```

The script performs these checks:

1. a complete `lake build` with no warnings or errors;
2. explicit `#print axioms` inspection of the public, real, complex, and finite
   theorem entry points;
3. absence of `sorry`, `admit`, and `sorryAx` in committed Lean sources;
4. absence of custom axioms, postulates, opaque declarations, and unsafe
   declarations;
5. absence of provisional module names and internal development markers;
6. confirmation that `GleasonStatement.lean` imports only Mathlib.

The expected logical dependencies are:

```text
propext
Classical.choice
Quot.sound
```

These are standard dependencies of Mathlib developments using quotients,
classical choice, and propositional extensionality.

## Lint policy

The Lake configuration disables seven suggestion-only editorial linters for
the internal proof corpus. These options affect neither elaboration nor kernel
checking. All remaining Lean warnings and errors are retained, and the
verification script rejects any such diagnostic.

## Comparator

The manually triggered GitHub workflow `.github/workflows/comparator.yml`
constructs a trusted `Challenge.lean` from the public statement, then asks the
[Lean comparator](https://github.com/leanprover/comparator) to verify that

```text
ClassicalGleason.Separable.gleason_theorem_verified
```

has exactly the challenge type, uses only the permitted axioms, and is accepted
by the Lean kernel. The challenge import closure contains only
`GleasonStatement.lean` and Mathlib.

Comparator's adversarial sandbox guarantee requires Linux with a functioning
`landrun`. A macOS run using comparator's development shim is useful for setup
testing but is not equivalent to the Linux sandboxed check.

The workflow does not compile the solution before invoking comparator, does
not restore a project build cache, and removes persisted checkout credentials.
Comparator performs the challenge and solution builds and exports under its
pinned `landrun` sandbox. External actions and comparator tools are pinned to
immutable revisions.

Comparator is an additional audit layer. It does not replace review of whether
the formal statement accurately expresses the intended mathematical theorem.
