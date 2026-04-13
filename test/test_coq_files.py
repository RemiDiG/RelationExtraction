import sys
from subprocess import call

for f in sys.argv[2:]:
    ret = call([sys.argv[1], "-I", "..", "-R", "..", "RelationExtraction", f])
    if ret == 0:
        print("Extraction to Rocq (%s): SUCCESS." % f)
    else:
        print("Extraction to Rocq (%s): ERROR." % f)
        sys.exit(1)
