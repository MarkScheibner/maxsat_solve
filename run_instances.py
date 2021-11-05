import subprocess
from os import listdir
import os
import sys
from multiprocessing import Pool

if len(sys.argv) != 5:
	print(f"Usage: python {sys.argv[0]} /path/to/instances /path/to/instancelist timeout threads")
	exit(1)


instances = []
with open(sys.argv[2]) as instancelist:
	instances = list(map(lambda s: s.strip().split(", "), instancelist.readlines()))
timeout = int(sys.argv[3])
threads = int(sys.argv[4])

print("name, mode, nodes, edges, components, maxdeg, mindeg, preproc-reduction, tree-width, success")

def do_instance(instance):
	name, mode = instance
	try:
		command = ["cargo", "run", "--release", "--quiet", "--", "--file", f"{sys.argv[1]}/{name}", "-c", mode]
		p = subprocess.run(command, stdout=subprocess.PIPE, encoding="UTF-8", timeout=timeout)
		if p.returncode == 0:
			return f"{name}, {mode}, {p.stdout.strip()}, 0"
		else:
			return f"{name}, {mode}, {p.stdout.strip()}, 1"
	except subprocess.TimeoutExpired as exc:
		if exc.stdout:
			return f"{name}, {mode}, {exc.stdout.strip()}, 2"
		else:
			return f"{name}, {mode}, -1, -1, -1, -1, -1, -1, -1, -1"

with Pool(threads) as p:
	for result in p.map(do_instance, instances):
		print(result)
