#!/usr/bin/env python3
"""
Quick verification script to check if the Lab 2 setup is working correctly.
This script tests all major components without running the full test suite.
"""

import os
import sys
import time
from typing import Dict, Any

def categorize_lean_error(error_msg: str) -> str:
    """More granular error categorization for better feedback"""
    if "type mismatch" in error_msg:
        return "TYPE_ERROR"
    elif "tactic failed" in error_msg:
        return "PROOF_TACTIC_ERROR"


def check_environment() -> Dict[str, Any]:
    """Check if the basic environment is set up correctly."""
    print("🔍 Checking environment setup...")
    
    results = {
        "python_version": sys.version,
        "working_directory": os.getcwd(),
        "lab2_directory": os.path.exists("src") and os.path.exists("tasks"),
        "lean_available": False,
        "api_key_present": bool(os.getenv("OPENAI_API_KEY"))
    }
    
    # Check if Lean is available
    try:
        import subprocess
        result = subprocess.run(["lake", "--version"], capture_output=True, text=True, timeout=10)
        results["lean_available"] = result.returncode == 0
        if results["lean_available"]:
            results["lean_version"] = result.stdout.strip()
    except Exception as e:
        results["lean_error"] = str(e)
    
    # Print results
    print(f"✅ Python Version: {sys.version.split()[0]}")
    print(f"📁 Working Directory: {os.getcwd()}")
    print(f"📂 Lab2 Structure: {'✅' if results['lab2_directory'] else '❌'}")
    print(f"🏗️  Lean Available: {'✅' if results['lean_available'] else '❌'}")
    print(f"🔑 API Key Present: {'✅' if results['api_key_present'] else '❌'}")
    
    return results

def check_dependencies() -> Dict[str, Any]:
    """Check if required Python packages are installed."""
    print("\n🔍 Checking Python dependencies...")
    
    required_packages = [
        "openai", "numpy", "sentence_transformers", 
        "tiktoken", "requests", "beautifulsoup4", "pydantic"
    ]
    
    results = {"missing_packages": [], "installed_packages": []}
    
    for package in required_packages:
        try:
            __import__(package.replace("-", "_"))
            results["installed_packages"].append(package)
            print(f"✅ {package}")
        except ImportError:
            results["missing_packages"].append(package)
            print(f"❌ {package}")
    
    return results

def check_lean_execution() -> Dict[str, Any]:
    """Test basic Lean execution."""
    print("\n🔍 Testing Lean execution...")
    
    # Simple Lean code to test
    test_code = """
def test_function (x : Nat) : Nat := x

#check test_function
"""
    
    try:
        from src.lean_runner import execute_lean_code
        result = execute_lean_code(test_code)
        
        success = "executed successfully" in result
        print(f"🏗️  Lean Execution: {'✅' if success else '❌'}")
        
        if not success and "Lean Error:" in result:
            error = result.split("Lean Error:")[1].strip()[:100]
            print(f"   Error: {error}...")
        
        return {"lean_execution": success, "result": result}
        
    except Exception as e:
        print(f"❌ Lean execution failed: {e}")
        return {"lean_execution": False, "error": str(e)}

def check_database_creation() -> Dict[str, Any]:
    """Test database creation capability."""
    print("\n🔍 Testing database creation...")
    
    results = {
        "openai_db_exists": os.path.exists("database.npy"),
        "mini_db_exists": os.path.exists("database_mini.npy"),
        "documents_exist": os.path.exists("documents") and len(os.listdir("documents")) > 0
    }
    
    print(f"📊 OpenAI Database: {'✅' if results['openai_db_exists'] else '❌'}")
    print(f"📊 MiniLM Database: {'✅' if results['mini_db_exists'] else '❌'}")
    print(f"📚 Documents Directory: {'✅' if results['documents_exist'] else '❌'}")
    
    # Try to create database if none exist
    if not (results['openai_db_exists'] or results['mini_db_exists']):
        print("🔧 Attempting to create database...")
        try:
            import create_database
            success = create_database.create_database()
            results["database_creation"] = success
            print(f"🔧 Database Creation: {'✅' if success else '❌'}")
        except Exception as e:
            results["database_creation_error"] = str(e)
            print(f"❌ Database creation failed: {e}")
    
    return results

def test_single_task() -> Dict[str, Any]:
    """Test a single simple task end-to-end."""
    print("\n🔍 Testing simple task (task_id_0)...")
    
    try:
        from src.main import main_workflow, get_problem_and_code_from_taskpath
        
        # Test the simplest task (identity function)
        task_path = "tasks/task_id_0"
        
        if not os.path.exists(task_path):
            return {"error": "Task directory not found"}
        
        # Get problem and template
        problem_description, lean_code_template = get_problem_and_code_from_taskpath(task_path)
        
        # Generate solution
        start_time = time.time()
        solution = main_workflow(problem_description, lean_code_template)
        runtime = time.time() - start_time
        
        # Check solution quality
        has_code = solution["code"] != "sorry" and len(solution["code"]) > 0
        has_proof = solution["proof"] != "sorry" and len(solution["proof"]) > 0
        
        print(f"⚡ Runtime: {runtime:.2f} seconds")
        print(f"💻 Generated Code: {'✅' if has_code else '❌'}")
        print(f"📜 Generated Proof: {'✅' if has_proof else '❌'}")
        
        # Test the generated solution
        try:
            from src.lean_runner import execute_lean_code
            
            full_code = lean_code_template.replace("{{code}}", solution["code"]).replace("{{proof}}", solution["proof"])
            test_result = execute_lean_code(full_code)
            
            success = "executed successfully" in test_result
            print(f"🧪 Solution Test: {'✅' if success else '❌'}")
            
            return {
                "runtime": runtime,
                "has_code": has_code,
                "has_proof": has_proof,
                "solution_works": success,
                "test_result": test_result
            }
            
        except Exception as e:
            print(f"❌ Solution testing failed: {e}")
            return {
                "runtime": runtime,
                "has_code": has_code,
                "has_proof": has_proof,
                "solution_works": False,
                "error": str(e)
            }
    
    except Exception as e:
        print(f"❌ Task testing failed: {e}")
        return {"error": str(e)}

def check_agent_availability() -> Dict[str, Any]:
    """Check if AI agents are available."""
    print("\n🔍 Testing agent availability...")
    
    results = {}
    
    try:
        from src.agents import create_agent_with_fallback
        
        # Test LLM agent
        llm_agent = create_agent_with_fallback("gpt-4o", "llm")
        llm_available = llm_agent.is_available() if hasattr(llm_agent, 'is_available') else True
        results["llm_agent"] = llm_available
        print(f"🤖 LLM Agent: {'✅' if llm_available else '❌ (fallback)'}")
        
        # Test reasoning agent
        reasoning_agent = create_agent_with_fallback("o3-mini", "reasoning")
        reasoning_available = reasoning_agent.is_available() if hasattr(reasoning_agent, 'is_available') else True
        results["reasoning_agent"] = reasoning_available
        print(f"🧠 Reasoning Agent: {'✅' if reasoning_available else '❌ (fallback)'}")
        
    except Exception as e:
        print(f"❌ Agent testing failed: {e}")
        results["error"] = str(e)
    
    return results

def generate_report(all_results: Dict[str, Any]) -> str:
    """Generate a summary report of all checks."""
    
    # Calculate overall health score
    checks = [
        all_results.get("environment", {}).get("lab2_directory", False),
        all_results.get("environment", {}).get("lean_available", False),
        all_results.get("dependencies", {}).get("missing_packages", []) == [],
        all_results.get("lean_execution", {}).get("lean_execution", False),
        all_results.get("task_test", {}).get("solution_works", False)
    ]
    
    health_score = sum(checks) / len(checks) * 100
    
    report = f"""
{'='*60}
LAB 2 SETUP VERIFICATION REPORT
{'='*60}

Overall Health Score: {health_score:.1f}%

ENVIRONMENT:
  ✓ Lab2 Structure: {all_results.get("environment", {}).get("lab2_directory", False)}
  ✓ Lean Available: {all_results.get("environment", {}).get("lean_available", False)}
  ✓ API Key Present: {all_results.get("environment", {}).get("api_key_present", False)}

DEPENDENCIES:
  ✓ Missing Packages: {len(all_results.get("dependencies", {}).get("missing_packages", []))}
  ✓ Installed Packages: {len(all_results.get("dependencies", {}).get("installed_packages", []))}

FUNCTIONALITY:
  ✓ Lean Execution: {all_results.get("lean_execution", {}).get("lean_execution", False)}
  ✓ Database Available: {all_results.get("database", {}).get("openai_db_exists", False) or all_results.get("database", {}).get("mini_db_exists", False)}
  ✓ Task Solution: {all_results.get("task_test", {}).get("solution_works", False)}

AGENTS:
  ✓ LLM Agent: {all_results.get("agents", {}).get("llm_agent", False)}
  ✓ Reasoning Agent: {all_results.get("agents", {}).get("reasoning_agent", False)}

RECOMMENDATIONS:
"""
    
    # Add specific recommendations
    if health_score >= 90:
        report += "  🎉 System is fully functional! Ready for submission.\n"
    elif health_score >= 75:
        report += "  ✅ System is mostly functional with minor issues.\n"
    elif health_score >= 50:
        report += "  ⚠️  System has some issues but should work with fallbacks.\n"
    else:
        report += "  ❌ System needs attention before use.\n"
    
    # Specific fixes
    if not all_results.get("environment", {}).get("lean_available", False):
        report += "  • Install Lean 4: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh\n"
    
    if all_results.get("dependencies", {}).get("missing_packages", []):
        report += "  • Install missing packages: pip install -r requirements.txt\n"
    
    if not (all_results.get("database", {}).get("openai_db_exists", False) or all_results.get("database", {}).get("mini_db_exists", False)):
        report += "  • Create database: python create_database.py\n"
    
    report += f"\n{'='*60}\n"
    
    return report

def main():
    """Run all verification checks."""
    print("🚀 Starting Lab 2 Setup Verification")
    print("=" * 60)
    
    all_results = {}
    
    # Run all checks
    all_results["environment"] = check_environment()
    all_results["dependencies"] = check_dependencies()
    all_results["lean_execution"] = check_lean_execution()
    all_results["database"] = check_database_creation()
    all_results["agents"] = check_agent_availability()
    all_results["task_test"] = test_single_task()
    
    # Generate and print report
    report = generate_report(all_results)
    print(report)
    
    # Save results
    try:
        import json
        with open("verification_results.json", "w") as f:
            json.dump(all_results, f, indent=2, default=str)
        print("📁 Detailed results saved to verification_results.json")
    except Exception as e:
        print(f"❌ Could not save results: {e}")
    
    return all_results

if __name__ == "__main__":
    results = main() 