# Configuration

## Local service
Python 3.10+ and optional Lean via elan. The repository pins Lean 4.19.0. Use python server.py --project /absolute/path for built Lake projects. The service binds to loopback and is not a sandbox.

## Optional AI
Set LEANDUET_AI_URL to the full OpenAI-compatible chat-completions endpoint, LEANDUET_AI_MODEL and optionally LEANDUET_AI_KEY. Requests require consent and send proof source and notes to the configured provider. Outputs are proposals, not verification.

## Informath
Install upstream independently; set LEANDUET_INFORMATH_ROOT and optionally LEANDUET_INFORMATH_BIN and LEANDUET_INFORMATH_TOOLCHAIN. Compatibility with an installed upstream runtime remains unverified.

## Development
Run node --test tests/*.test.mjs, python -m unittest discover -s tests, lean examples/Compose.lean, lean lean/TMN.lean, lean lean/Dependent.lean and the semantic integration scripts. For browser tests install playwright and Chromium. See .github/workflows/ci.yml and .github/workflows/pages.yml.
