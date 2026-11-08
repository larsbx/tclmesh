import importlib.util
import sys
spec = importlib.util.spec_from_file_location('q45_real_worker', '/workspace/scratch/20faefa4e70a/tclmesh/tools/q45_result_store.py')
worker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(worker)
original = worker.handle
def lose_commit_reply(db, fields):
    response = original(db, fields)
    return b'lost_commit_response' if fields[0] == b'commit' else response
worker.handle = lose_commit_reply
raise SystemExit(worker.main())
