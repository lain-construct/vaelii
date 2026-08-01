<!-- Thanks for contributing. The sections below mirror CONTRIBUTING.md;
     please fill them in rather than deleting them. -->

## Summary

<!-- What does this PR change, and why? -->

Closes #<!-- issue number; use "Refs #N" for a related-but-not-closing issue, or delete this line if none -->

## Testing

<!-- How was this verified? `lein gate` output, test namespaces run, new tests added,
     manual checks. See CONTRIBUTING.md §5. -->

## Breaking changes

<!-- Renaming or removing anything on `vaelii.core` is breaking (CONTRIBUTING.md §4.4).
     Describe the break and the migration, or write "None". -->

None

## Checklist

- [ ] Commit subjects follow `type(scope): subject` (CONTRIBUTING.md §7).
- [ ] Every commit is signed off under the DCO (`git commit -s`; CONTRIBUTING.md §9.4).
- [ ] I have signed the CLA via cla-assistant (CONTRIBUTING.md §9.5).
- [ ] Any `Co-Authored-By:` / `Co-developed-by:` trailers credit human collaborators
      only (CONTRIBUTING.md §7).
- [ ] New features and bug fixes have tests; a bug-fix test fails before the fix and
      passes after (CONTRIBUTING.md §5).
- [ ] `lein gate` passes locally — lint, the suite, and the perf claims.
- [ ] Ran `./scripts/test-backends.sh` if this touches storage, the index, records,
      recovery or overlay; the failing set must be identical across all eight
      (CONTRIBUTING.md §5).
- [ ] Ran `lein test :all` if this touches inference, indexing or the TMS
      (CONTRIBUTING.md §5).
- [ ] Anything added to `vaelii.core` has a docstring and an entry in `docs/api.md`;
      any behaviour change updates the doc that describes it (CONTRIBUTING.md §8).
- [ ] Comments and docs describe the code as it is now — no "was", "previously", or
      migration narration (CONTRIBUTING.md §3.6).
- [ ] Didn't `--no-verify` or amend already-pushed commits (CONTRIBUTING.md §7).
