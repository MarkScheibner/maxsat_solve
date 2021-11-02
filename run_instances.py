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
	instances = list(map(lambda s: s.strip(), instancelist.readlines()))
num_instances = len(instances)
timeout = int(sys.argv[3])
threads = int(sys.argv[4])

print("name, mode, nodes, edges, components, maxdeg, mindeg, preproc-reduction, tree-width, success")

def do_instance(instance):
	results = []

	for mode in ["-p", "-d", "-i"]:
		try:
			command = ["cargo", "run", "--release", "--quiet", "--", "--file", f"{sys.argv[1]}/{instance}", "-c", mode]
			p = subprocess.run(command, stdout=subprocess.PIPE, encoding="UTF-8", timeout=timeout)
			if p.returncode == 0:
				results.append(f"{instance}, {mode}, {p.stdout.strip()}, 0")
			else:
				results.append(f"{instance}, {mode}, {p.stdout.strip()}, 1")
		except subprocess.TimeoutExpired as exc:
			if exc.stdout:
				results.append(f"{instance}, {mode}, {exc.stdout.strip()}, 2")
			else:
				results.append(f"{instance}, {mode}, -1, -1, -1, -1, -1, -1, -1, -1")
	
	return results

results = []
with Pool(threads) as p:
	for result in p.map(do_instance, instances):
		for run in result:
			print(run)
