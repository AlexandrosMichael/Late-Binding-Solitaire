# !/bin/bash
find ./UnsolvableInstances -type f ! -name '*.param' -delete
find ./SolvableInstances -type f ! -name '*.param' -delete
find ./GeneratedInstances -type f ! -name '*.param' -delete

