#!/usr/bin/python3
import dict_hash
import json
import os
import random
import subprocess

SPEC_JSON_FILE = "./mutation/raft.json"
SPEC_TLA_FILE = "./mutation/raft.tla"
MUTATION_CFG_FILE = "./mutation/config.json"
MUTANT_DIR = "./mutation/mutants/"

# Exponential distribution gives rise to deeper mutations
def mutations_to_perform(mutations_remaining):
    return min(int(random.expovariate(1)), mutations_remaining)

def mutate(ast_node, mutations_remaining=1):
    if mutations_remaining == 0:
        return (ast_node, mutations_remaining)

    if len(ast_node.keys()) >= 2:
        if "let" in ast_node.keys():
            # LET-IN construct
            # For now, we only modify the IN part
            return mutate(ast_node["body"], mutations_remaining)
        else:
            return (ast_node, mutations_remaining)

    elif len(ast_node.keys()) == 1:
        node_type = list(ast_node.keys())[0]
        mutated = ast_node

        while mutations_remaining > 0:
            # We encourage deeper mutations by picking the number of mutations to perform
            # at each level from an exponential distribution with mean 1
            mutations_at_this_level = mutations_to_perform(mutations_remaining)
            node_body = mutated[node_type]

            # Python 3.10 (currently in beta) introduces structural pattern matching
            match node_type:
                case "and":
                    # Select a clause
                    clause = random.randrange(0, len(node_body))
                    options = ["drop", "mutate"] if len(node_body) > 1 and mutations_at_this_level > 0 else ["mutate"]
                    match random.choice(options):
                        case "drop":
                            # mutable state :-(
                            removed = node_body.pop(clause)
                            mutated = {"and": node_body}
                            mutations_remaining -= 1
                        case "mutate":
                            mutated_clause, rem = mutate(node_body[clause], mutations_remaining)
                            mutated["and"][clause] = mutated_clause
                            mutations_remaining = rem
                # Don't go into an infinite loop for unsupported AST nodes
                case _:
                    break
                            
        return (mutated, mutations_remaining)
    else:
        return (mutated, mutations_remaining)

if __name__ == "__main__":
    cfg = None
    ast = None
    # Maps operator names to index in ast["declarations"]
    defs = {}

    with open(MUTATION_CFG_FILE) as f:
        cfg = json.load(f)

    with open(SPEC_JSON_FILE) as f:
        ast = json.load(f)

    for decl_id, decl in enumerate(ast["declarations"]):
        if "operator" in decl:
            name = decl["operator"]
            defs[name] = decl_id

    actions = cfg["actionsToMutate"]
    successful = False
    mutants = 0

    # Generate mutations until one parses
    while not successful:
        # Select a random action to mutate
        action = random.choice(actions)

        print(f"Mutating {action}")

        # Perform mutations on a copy of the AST
        _ast = ast
        # Mutate the action
        decl = _ast["declarations"][defs[action]]
        mutated, _ = mutate(decl["body"])
        decl["body"] = mutated
        _ast["declarations"][defs[action]] = decl

        mutants += 1

        # Give the mutant a name
        name = f"{action}_" + dict_hash.sha256(_ast)
        MUTATED_SPEC_JSON_FILE = os.path.join(MUTANT_DIR, f"{name}.json")
        MUTATED_SPEC_TLA_FILE = os.path.join(MUTANT_DIR, f"{name}.tla")
        os.makedirs(MUTANT_DIR, exist_ok=True)

        print(f"Generated {name} ({mutants} mutants)")
        
        # Create JSON file for the mutated spec
        with open(MUTATED_SPEC_JSON_FILE, "w") as f:
            json.dump(_ast, f)
        
        # Try to convert the JSON to TLA
        cmd = ["~/apalache/bin/apalache-mc", "parse", f"--output={MUTATED_SPEC_TLA_FILE}", MUTATED_SPEC_JSON_FILE]
        # Use WSL if running from Windows
        if os.name == 'nt':
            cmd = ['wsl'] + cmd

        print(cmd)

        subprocess.check_call(cmd)
        # Apalache returns 0 even if the JSON fails to parse, so instead we check that the TLA file is created
        if os.path.exists(MUTATED_SPEC_TLA_FILE):
            successful = True
        else:
            raise Exception("Mutant fails to parse.")
        
        # Remove the JSON: we can always get it from the TLA
        os.remove(MUTATED_SPEC_JSON_FILE)
        
