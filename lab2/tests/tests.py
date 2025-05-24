import os
import sys
import time
import json
from datetime import datetime
from typing import Dict, List, Any, Tuple
from dataclasses import dataclass

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from src.main import (
    main_workflow, 
    get_problem_and_code_from_taskpath, 
    get_unit_tests_from_taskpath, 
    get_task_lean_template_from_taskpath
)
from src.lean_runner import execute_lean_code

@dataclass
class TestResult:
    """Data class to store test results for a single task."""
    task_id: str
    passes_unit_tests: bool
    proof_is_correct: bool
    runtime: float
    implementation_error: str = ""
    proof_error: str = ""
    generated_code_length: int = 0
    generated_proof_length: int = 0
    used_api: bool = False
    used_fallback: bool = False

class TestReporter:
    """Handles test reporting and metrics collection."""
    
    def __init__(self):
        self.results: List[TestResult] = []
        self.start_time = time.time()
        
    def add_result(self, result: TestResult):
        """Add a test result to the collection."""
        self.results.append(result)
        
    def generate_summary(self) -> Dict[str, Any]:
        """Generate comprehensive test summary."""
        total_tests = len(self.results)
        if total_tests == 0:
            return {"error": "No tests run"}
        
        implementation_passes = sum(1 for r in self.results if r.passes_unit_tests)
        proof_passes = sum(1 for r in self.results if r.proof_is_correct)
        api_usage = sum(1 for r in self.results if r.used_api)
        fallback_usage = sum(1 for r in self.results if r.used_fallback)
        
        total_runtime = sum(r.runtime for r in self.results)
        avg_runtime = total_runtime / total_tests
        
        summary = {
            "test_metadata": {
                "total_tests": total_tests,
                "timestamp": datetime.now().isoformat(),
                "total_runtime": round(total_runtime, 2),
                "average_runtime": round(avg_runtime, 2)
            },
            "implementation_results": {
                "passes": implementation_passes,
                "failures": total_tests - implementation_passes,
                "success_rate": round((implementation_passes / total_tests) * 100, 1)
            },
            "proof_results": {
                "passes": proof_passes,
                "failures": total_tests - proof_passes,
                "success_rate": round((proof_passes / total_tests) * 100, 1)
            },
            "system_usage": {
                "api_calls": api_usage,
                "fallback_usage": fallback_usage,
                "api_rate": round((api_usage / total_tests) * 100, 1),
                "fallback_rate": round((fallback_usage / total_tests) * 100, 1)
            },
            "detailed_results": []
        }
        
        # Add detailed results for each task
        for result in self.results:
            summary["detailed_results"].append({
                "task_id": result.task_id,
                "implementation_pass": result.passes_unit_tests,
                "proof_pass": result.proof_is_correct,
                "runtime": round(result.runtime, 2),
                "code_length": result.generated_code_length,
                "proof_length": result.generated_proof_length,
                "used_api": result.used_api,
                "used_fallback": result.used_fallback,
                "implementation_error": result.implementation_error[:100] + "..." if len(result.implementation_error) > 100 else result.implementation_error,
                "proof_error": result.proof_error[:100] + "..." if len(result.proof_error) > 100 else result.proof_error
            })
        
        return summary
    
    def print_summary(self):
        """Print a formatted test summary to console."""
        summary = self.generate_summary()
        
        print("\n" + "=" * 80)
        print("TEST SUMMARY REPORT")
        print("=" * 80)
        
        # Test metadata
        metadata = summary["test_metadata"]
        print(f"Tests Run: {metadata['total_tests']}")
        print(f"Total Runtime: {metadata['total_runtime']} seconds")
        print(f"Average Runtime: {metadata['average_runtime']} seconds")
        print(f"Timestamp: {metadata['timestamp']}")
        
        # Implementation results
        impl = summary["implementation_results"]
        print(f"\nIMPLEMENTATION RESULTS:")
        print(f"  ✅ Passes: {impl['passes']}/{metadata['total_tests']} ({impl['success_rate']}%)")
        print(f"  ❌ Failures: {impl['failures']}/{metadata['total_tests']}")
        
        # Proof results
        proof = summary["proof_results"]
        print(f"\nPROOF RESULTS:")
        print(f"  ✅ Passes: {proof['passes']}/{metadata['total_tests']} ({proof['success_rate']}%)")
        print(f"  ❌ Failures: {proof['failures']}/{metadata['total_tests']}")
        
        # System usage
        usage = summary["system_usage"]
        print(f"\nSYSTEM USAGE:")
        print(f"  🌐 API Calls: {usage['api_calls']}/{metadata['total_tests']} ({usage['api_rate']}%)")
        print(f"  🔧 Fallback Usage: {usage['fallback_usage']}/{metadata['total_tests']} ({usage['fallback_rate']}%)")
        
        # Detailed results table
        print(f"\nDETAILED RESULTS:")
        print("-" * 80)
        print(f"{'Task':<12} {'Impl':<5} {'Proof':<5} {'Time':<6} {'API':<4} {'Fall':<4} {'Error':<20}")
        print("-" * 80)
        
        for result in summary["detailed_results"]:
            impl_status = "✅" if result["implementation_pass"] else "❌"
            proof_status = "✅" if result["proof_pass"] else "❌"
            api_status = "Yes" if result["used_api"] else "No"
            fallback_status = "Yes" if result["used_fallback"] else "No"
            
            error_msg = result["implementation_error"] or result["proof_error"]
            error_preview = error_msg[:18] + ".." if len(error_msg) > 20 else error_msg
            
            print(f"{result['task_id']:<12} {impl_status:<5} {proof_status:<5} {result['runtime']:<6.1f} {api_status:<4} {fallback_status:<4} {error_preview:<20}")
        
        print("=" * 80)
        
        # Overall assessment
        overall_score = (impl['success_rate'] + proof['success_rate']) / 2
        print(f"\nOVERALL ASSESSMENT: {overall_score:.1f}%")
        
        if overall_score >= 90:
            print("🎉 EXCELLENT: System performing at high level!")
        elif overall_score >= 75:
            print("✅ GOOD: System performing well with minor issues")
        elif overall_score >= 50:
            print("⚠️  ACCEPTABLE: System functional but needs improvement")
        else:
            print("❌ NEEDS WORK: System requires significant improvements")
    
    def save_to_file(self, filename: str = "test_results.json"):
        """Save test results to JSON file."""
        summary = self.generate_summary()
        
        try:
            with open(filename, 'w') as f:
                json.dump(summary, f, indent=2)
            print(f"\n📁 Test results saved to {filename}")
        except Exception as e:
            print(f"❌ Failed to save results to {filename}: {e}")

def analyze_lean_error(error_output: str) -> Tuple[str, bool]:
    """
    Analyze Lean error output to categorize the error type.
    
    Args:
        error_output: Raw error output from Lean
        
    Returns:
        Tuple of (error_category, is_implementation_error)
    """
    if "executed successfully" in error_output:
        return "SUCCESS", False
    
    if "Lean Error:" not in error_output:
        return "UNKNOWN_ERROR", True
    
    error_content = error_output.split("Lean Error:")[1].strip().lower()
    
    # Implementation errors
    if any(keyword in error_content for keyword in ["type mismatch", "function expected", "syntax error", "unexpected token"]):
        return "IMPLEMENTATION_ERROR", True
    
    # Proof errors
    if any(keyword in error_content for keyword in ["tactic failed", "unsolved goals", "proof incomplete"]):
        return "PROOF_ERROR", False
    
    # Other errors
    if "timeout" in error_content:
        return "TIMEOUT", False
    
    return "UNKNOWN_ERROR", True

def test_single_task(task_id: str, reporter: TestReporter) -> TestResult:
    """
    Test a single task and return detailed results.
    
    Args:
        task_id: Task identifier (e.g., "task_id_227")
        reporter: TestReporter instance for logging
        
    Returns:
        TestResult object with comprehensive test data
    """
    print(f"\n{'='*20} Testing {task_id} {'='*20}")
    
    # Initialize result object
    result = TestResult(
        task_id=task_id,
        passes_unit_tests=False,
        proof_is_correct=False,
        runtime=0.0
    )
    
    try:
        task_path = f"tasks/{task_id}"
        
        # Check if task exists
        if not os.path.exists(task_path):
            print(f"❌ Task directory not found: {task_path}")
            result.implementation_error = "Task directory not found"
            return result
        
        # Read task files
        print(f"📖 Reading task files...")
        problem_description, lean_code_template = get_problem_and_code_from_taskpath(task_path)
        unit_tests = get_unit_tests_from_taskpath(task_path)
        
        print(f"📝 Problem description: {len(problem_description)} chars")
        print(f"🧪 Unit tests: {len(unit_tests)} chars")
        
        # Generate solution
        print(f"🤖 Generating solution...")
        start_time = time.time()
        
        try:
            generated_solution = main_workflow(problem_description, lean_code_template)
            result.runtime = time.time() - start_time
            
            generated_code = generated_solution["code"]
            generated_proof = generated_solution["proof"]
            
            result.generated_code_length = len(generated_code)
            result.generated_proof_length = len(generated_proof)
            
            # Determine if API or fallback was used
            if "sorry" in generated_code or "sorry" in generated_proof:
                result.used_fallback = True
            else:
                # Assume API was used if we got non-sorry results
                result.used_api = True
            
            print(f"✅ Solution generated in {result.runtime:.2f}s")
            print(f"📊 Code: {result.generated_code_length} chars, Proof: {result.generated_proof_length} chars")
            
        except Exception as e:
            result.runtime = time.time() - start_time
            result.implementation_error = f"Solution generation failed: {str(e)}"
            print(f"❌ Solution generation failed: {e}")
            return result
        
        # Test implementation only
        print(f"🔍 Testing implementation...")
        task_lean_template = get_task_lean_template_from_taskpath(task_path)
        
        implementation_code = task_lean_template.replace("{{code}}", generated_code).replace("{{proof}}", "sorry")
        implementation_code += f"\n\n{unit_tests}"
        
        implementation_result = execute_lean_code(implementation_code)
        error_category, is_impl_error = analyze_lean_error(implementation_result)
        
        if error_category == "SUCCESS":
            result.passes_unit_tests = True
            print("✅ Implementation passes unit tests")
        else:
            result.implementation_error = implementation_result.split("Lean Error:")[1].strip() if "Lean Error:" in implementation_result else implementation_result
            print(f"❌ Implementation failed: {error_category}")
        
        # Test full solution (implementation + proof)
        print(f"🔍 Testing proof...")
        full_code = task_lean_template.replace("{{code}}", generated_code).replace("{{proof}}", generated_proof)
        full_code += f"\n\n{unit_tests}"
        
        proof_result = execute_lean_code(full_code)
        error_category, is_impl_error = analyze_lean_error(proof_result)
        
        if error_category == "SUCCESS":
            result.proof_is_correct = True
            print("✅ Proof is correct")
        else:
            result.proof_error = proof_result.split("Lean Error:")[1].strip() if "Lean Error:" in proof_result else proof_result
            print(f"❌ Proof failed: {error_category}")
        
        # Final status
        if result.passes_unit_tests and result.proof_is_correct:
            print("🎉 Task completed successfully!")
        elif result.passes_unit_tests:
            print("⚠️  Implementation works but proof has issues")
        else:
            print("❌ Task failed")
            
    except Exception as e:
        result.implementation_error = f"Test execution failed: {str(e)}"
        print(f"💥 Test execution failed: {e}")
    
    return result

def test_all_tasks(task_list: List[str] = None) -> TestReporter:
    """
    Test all specified tasks and return comprehensive results.
    
    Args:
        task_list: List of task IDs to test. If None, uses default list.
        
    Returns:
        TestReporter with all results
    """
    if task_list is None:
        task_list = [0, 58, 77, 127, 227, 404, 431, 433, 435, 441, 447]
        task_list = [f"task_id_{task_id}" for task_id in task_list]
    
    print("🚀 STARTING COMPREHENSIVE TEST SUITE")
    print("=" * 80)
    print(f"📋 Testing {len(task_list)} tasks: {', '.join(task_list)}")
    
    reporter = TestReporter()
    
    for i, task_id in enumerate(task_list, 1):
        print(f"\n🔄 Progress: {i}/{len(task_list)}")
        
        result = test_single_task(task_id, reporter)
        reporter.add_result(result)
        
        # Quick status update
        status = "✅" if result.passes_unit_tests and result.proof_is_correct else "❌"
        print(f"{status} {task_id}: Impl={result.passes_unit_tests}, Proof={result.proof_is_correct}, Time={result.runtime:.1f}s")
    
    return reporter

def run_performance_benchmark():
    """Run a focused performance benchmark on key tasks."""
    print("\n🏃 RUNNING PERFORMANCE BENCHMARK")
    print("-" * 40)
    
    # Test a subset of representative tasks
    benchmark_tasks = ["task_id_0", "task_id_227", "task_id_404"]  # Simple, medium, complex
    
    start_time = time.time()
    reporter = test_all_tasks(benchmark_tasks)
    total_time = time.time() - start_time
    
    summary = reporter.generate_summary()
    
    print(f"\n📊 BENCHMARK RESULTS:")
    print(f"   Tasks: {len(benchmark_tasks)}")
    print(f"   Total Time: {total_time:.2f}s")
    print(f"   Avg Time/Task: {total_time/len(benchmark_tasks):.2f}s")
    print(f"   Success Rate: {(summary['implementation_results']['success_rate'] + summary['proof_results']['success_rate'])/2:.1f}%")
    
    return reporter

def main():
    """Main test execution function."""
    import argparse
    
    parser = argparse.ArgumentParser(description='Comprehensive test runner for Lean 4 coding agent')
    parser.add_argument('--benchmark', action='store_true', help='Run performance benchmark only')
    parser.add_argument('--task', type=str, help='Test single task (e.g., task_id_227)')
    parser.add_argument('--save', type=str, default='test_results.json', help='Save results to file')
    parser.add_argument('--no-save', action='store_true', help='Skip saving results to file')
    
    args = parser.parse_args()
    
    try:
        if args.task:
            # Test single task
            print(f"🎯 Testing single task: {args.task}")
            reporter = TestReporter()
            result = test_single_task(args.task, reporter)
            reporter.add_result(result)
            
        elif args.benchmark:
            # Run benchmark
            reporter = run_performance_benchmark()
            
        else:
            # Test all tasks
            reporter = test_all_tasks()
        
        # Print summary
        reporter.print_summary()
        
        # Save results
        if not args.no_save:
            reporter.save_to_file(args.save)
        
        return reporter
        
    except KeyboardInterrupt:
        print("\n🛑 Testing interrupted by user")
        return None
    except Exception as e:
        print(f"💥 Test suite failed: {e}")
        return None

if __name__ == "__main__":
    result = main()