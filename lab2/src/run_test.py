from src.main import main_workflow
from src.lean_runner import execute_lean_code
import sys
import os

def run_test(task_id):
    """
    Run a single test on a specific task.
    
    Args:
        task_id: The ID of the task to test (e.g., "0", "58")
    """
    task_path = f"tasks/task_id_{task_id}"
    
    # Check if the task exists
    if not os.path.exists(task_path):
        print(f"Task {task_id} not found!")
        return
    
    # Read problem description and template
    with open(os.path.join(task_path, "description.txt"), "r") as f:
        problem_description = f.read()
    
    with open(os.path.join(task_path, "task.lean"), "r") as f:
        task_lean_code = f.read()
    
    # Run the main workflow
    print(f"Running main workflow for task {task_id}...")
    implementation = main_workflow(problem_description, task_lean_code)
    
    print("\nGenerated Code:")
    print(implementation["code"])
    
    print("\nGenerated Proof:")
    print(implementation["proof"])
    
    # Test the code
    print("\nTesting implementation...")
    implementation_code = task_lean_code.replace("{{code}}", implementation["code"]).replace("{{proof}}", "sorry")
    result = execute_lean_code(implementation_code)
    print(f"Implementation result: {'Success' if 'executed successfully' in result else 'Failure'}")
    
    # Test the proof
    print("\nTesting proof...")
    full_code = task_lean_code.replace("{{code}}", implementation["code"]).replace("{{proof}}", implementation["proof"])
    result = execute_lean_code(full_code)
    print(f"Proof result: {'Success' if 'executed successfully' in result else 'Failure'}")
    
    if "Lean Error:" in result:
        print("\nError message:")
        print(result.split("Lean Error:")[1].strip())

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python run_test.py <task_id>")
        sys.exit(1)
    
    task_id = sys.argv[1]
    run_test(task_id)