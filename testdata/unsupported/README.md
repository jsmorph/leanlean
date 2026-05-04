# Unsupported Export Fixtures

These fixtures check the `unsupported` outcome for the independent export checker.  They are not rejected kernel terms.  They stop before declaration replay because the artifact asks for a Lean feature or export form outside the accepted NDJSON fragment.  The gap-report mode also uses these fixtures to verify that unsupported parser or importer entries appear as diagnostic rows rather than disappearing behind a bare parser failure.
