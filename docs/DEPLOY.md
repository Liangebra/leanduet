# Launch and deployment checklist

The static editor is safe to host as static files; it does not expose Lean or AI services. Never publish the Python checker as an unauthenticated public service.

## GitHub Pages (one-time repository admin action)

1. Open Settings → Pages.
2. Under Build and deployment, choose GitHub Actions.
3. Open Actions → Deploy browser-only demo → Run workflow (main).
4. After successful deployment, the workflow reports the actual site URL. Test it before sharing. Expected project URL: https://liangebra.github.io/leanduet/ (not live until deployment succeeds).

## Repository discoverability (admin UI)

- About → topics: lean4, mathlib, mathematics, theorem-proving, formal-verification, autoformalization, proof-assistant, latex, bidirectional-transformation, mathematical-reasoning.
- About → website: set to the deployed URL only after verification.
- Settings → General → Features → Discussions: enable. Keep Issues enabled. Use Q&A, Ideas and Announcements as discussion categories.
- Add a social preview image and pin the repository on the owner's profile if desired.
- Keep starter issues labeled "good first issue" / "help wanted". Use discussions for research ideas; issues for actionable changes.

## Release gates

Check CI and browser smoke test; verify the demo on desktop and mobile; capture a real short demo GIF or video; then share with Lean Zulip and mathematical communities. Do not advertise full unrestricted prose synchronization as implemented.
