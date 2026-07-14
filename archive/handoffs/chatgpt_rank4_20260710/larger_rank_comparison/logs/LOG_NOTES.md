# Notes on captured logs

Some expensive searches were not rerun to completion during packaging.  In particular:

- `rank8_exact.py` had previously been used as an exact fixed-algebra check, but can run slowly.  Prefer `rank8_polycheck.py`, which gives the cleaner exact fixed-algebra coefficient check.
- `mu8_fixed_exact_e4.py` has only a partial log here.  The weaker `mu8_e4_qonly.py` completed and found no candidate in the q-only subcheck.
- Files containing `sample` or `search` should be regarded as exploratory unless the log says a complete enumeration was done.
