# Contributing

Contributions should preserve the mathematical scope and verification standard
of the repository.

Run the complete verification routine before opening a pull request:

```sh
./scripts/verify.sh
```

The active source tree must remain free of build errors, warnings, placeholders,
custom axioms, unsafe declarations, and provisional development artifacts.
Changes to the public statement must update `docs/THEOREM.md` and the comparator
challenge in `.github/workflows/comparator.yml` in the same commit.

Material use of generative AI in a contribution should be disclosed in the pull
request description. Human contributors remain responsible for all submitted
code and mathematical claims.
