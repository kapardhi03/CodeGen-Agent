import os
import sys
import shutil
from typing import Tuple, Optional

sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from src.embedding_db import VectorDB
from src.embedding_models import OpenAIEmbeddingModel, MiniEmbeddingModel

def ensure_documents_exist():
    """
    Ensure documents directory exists with content for RAG.
    """
    print("Ensuring documents directory exists...")
    
    # Create documents directory if it doesn't exist
    os.makedirs("documents", exist_ok=True)
    
    # Check if there are any files in the documents directory
    document_files = [f for f in os.listdir("documents") if f.endswith('.txt')]
    
    if not document_files:
        print("No text files found in documents directory. Creating sample documents...")
        
        # Create comprehensive sample documents for Lean 4
        sample_docs = {
            "lean_basics.txt": """
# Lean 4 Basic Concepts

Lean 4 is a functional programming language and theorem prover. <EOC>

Basic syntax for function definitions:
def functionName (param: Type) : ReturnType := implementation <EOC>

Common proof tactics:
- rfl: reflexivity, proves a = a
- simp: simplification 
- exact: provide exact proof term
- constructor: build structure
- split: case analysis <EOC>

Basic types in Lean 4:
- Nat: natural numbers
- Int: integers  
- Bool: booleans
- Array: arrays
- List: lists <EOC>
""",
            
            "lean_proofs.txt": """
# Lean 4 Proof Examples

Example equality proof:
theorem add_zero (n : Nat) : n + 0 = n := by rfl <EOC>

Example conditional proof:
theorem if_example (a b : Int) : (if a ≤ b then a else b) ≤ a ∨ (if a ≤ b then a else b) ≤ b := by
  split
  · left; rfl
  · right; rfl <EOC>

Example constructor proof:
theorem pair_example (a b : Int) : ∃ x y, x = a ∧ y = b := by
  constructor
  · exact a
  · constructor
    · exact b
    · constructor <EOC>
""",
            
            "lean_implementations.txt": """
# Lean 4 Implementation Examples

Identity function:
def ident (x : Nat) : Nat := x <EOC>

Minimum of two integers:
def myMin (a b : Int) : Int := if a ≤ b then a else b <EOC>

Minimum of three integers:
def minOfThree (a b c : Int) : Int :=
  if a ≤ b then
    if a ≤ c then a else c
  else
    if b ≤ c then b else c <EOC>

Multiplication:
def multiply (a b : Int) : Int := a * b <EOC>

Array mapping:
def mapArray (f : Int → Int) (arr : Array Int) : Array Int := arr.map f <EOC>

Boolean operations:
def hasOppositeSign (a b : Int) : Bool := (a < 0 && b > 0) || (a > 0 && b < 0) <EOC>
""",
            
            "lean_specifications.txt": """
# Lean 4 Specification Examples

Specification for minimum function:
def myMin_spec (a b : Int) (result : Int) : Prop :=
  (result ≤ a ∧ result ≤ b) ∧ (result = a ∨ result = b) <EOC>

Specification for arithmetic:
def multiply_spec (a b : Int) (result : Int) : Prop := result = a * b <EOC>

Specification for boolean functions:
def hasOppositeSign_spec (a b : Int) (result : Bool) : Prop :=
  (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) ↔ result <EOC>

Specification for array operations:
def cubeElements_spec (a : Array Int) (result : Array Int) : Prop :=
  (result.size = a.size) ∧ (∀ i, i < a.size → result[i]! = a[i]! * a[i]! * a[i]!) <EOC>
"""
        }
        
        # Write sample documents
        for filename, content in sample_docs.items():
            filepath = os.path.join("documents", filename)
            with open(filepath, "w", encoding='utf-8') as f:
                f.write(content.strip())
            print(f"Created sample document: {filename}")
    
    # Verify we have content
    document_files = [f for f in os.listdir("documents") if f.endswith('.txt')]
    print(f"Documents directory contains {len(document_files)} text files: {', '.join(document_files)}")
    
    return len(document_files) > 0

def create_openai_database() -> Tuple[bool, Optional[str]]:
    """
    Create database using OpenAI embeddings.
    
    Returns:
        Tuple of (success, error_message)
    """
    try:
        print("Attempting to create database with OpenAI embeddings...")
        embedding_model = OpenAIEmbeddingModel()
        
        # Test if we can generate embeddings
        test_embedding = embedding_model.get_embedding("test")
        if not test_embedding:
            return False, "Failed to generate test embedding"
        
        vector_db = VectorDB(
            directory="documents",
            vector_file="database.npy",
            embedding_model=embedding_model
        )
        
        print("Successfully created database with OpenAI embeddings!")
        return True, None
        
    except Exception as e:
        error_msg = f"OpenAI database creation failed: {str(e)}"
        print(error_msg)
        return False, error_msg

def create_mini_database() -> Tuple[bool, Optional[str]]:
    """
    Create database using MiniLM embeddings.
    
    Returns:
        Tuple of (success, error_message)
    """
    try:
        print("Attempting to create database with MiniLM embeddings...")
        embedding_model = MiniEmbeddingModel()
        
        # Test if we can generate embeddings
        test_embedding = embedding_model.get_embedding("test")
        if not test_embedding:
            return False, "Failed to generate test embedding"
        
        vector_db = VectorDB(
            directory="documents",
            vector_file="database_mini.npy",
            embedding_model=embedding_model
        )
        
        print("Successfully created database with MiniLM embeddings!")
        return True, None
        
    except Exception as e:
        error_msg = f"MiniLM database creation failed: {str(e)}"
        print(error_msg)
        return False, error_msg

def verify_database(database_file: str) -> bool:
    """
    Verify that a database file exists and is valid.
    
    Args:
        database_file: Path to the .npy database file
        
    Returns:
        bool: True if database is valid, False otherwise
    """
    try:
        import numpy as np
        import pickle
        
        # Check if files exist
        if not os.path.exists(database_file):
            print(f"Database file {database_file} does not exist")
            return False
        
        chunks_file = os.path.splitext(database_file)[0] + "_chunks.pkl"
        if not os.path.exists(chunks_file):
            print(f"Chunks file {chunks_file} does not exist")
            return False
        
        # Try to load the files
        embeddings = np.load(database_file)
        with open(chunks_file, 'rb') as f:
            chunks = pickle.load(f)
        
        # Basic validation
        if len(embeddings) == 0:
            print("Database contains no embeddings")
            return False
        
        if len(chunks) == 0:
            print("Database contains no text chunks")
            return False
        
        if len(embeddings) != len(chunks):
            print(f"Mismatch: {len(embeddings)} embeddings but {len(chunks)} chunks")
            return False
        
        print(f"Database verification successful: {len(embeddings)} embeddings, {len(chunks)} chunks")
        return True
        
    except Exception as e:
        print(f"Database verification failed: {e}")
        return False

def cleanup_failed_database(database_file: str):
    """
    Clean up partially created database files.
    
    Args:
        database_file: Path to the .npy database file to clean up
    """
    try:
        chunks_file = os.path.splitext(database_file)[0] + "_chunks.pkl"
        
        if os.path.exists(database_file):
            os.remove(database_file)
            print(f"Removed incomplete database file: {database_file}")
        
        if os.path.exists(chunks_file):
            os.remove(chunks_file)
            print(f"Removed incomplete chunks file: {chunks_file}")
            
    except Exception as e:
        print(f"Error during cleanup: {e}")

def create_database():
    """
    Create the embedding database for RAG with comprehensive fallback strategy.
    """
    print("=" * 60)
    print("Creating embedding database for RAG system...")
    print("=" * 60)
    
    # Step 1: Ensure documents exist
    if not ensure_documents_exist():
        print("ERROR: Failed to create documents for database")
        return False
    
    # Step 2: Try to create OpenAI database first
    print("\n" + "-" * 40)
    print("Attempting OpenAI database creation...")
    print("-" * 40)
    
    openai_success, openai_error = create_openai_database()
    
    if openai_success and verify_database("database.npy"):
        print("\n✅ OpenAI database created and verified successfully!")
        print("Database file: database.npy")
        print("The system will use OpenAI embeddings for optimal performance.")
        return True
    else:
        print(f"\n❌ OpenAI database creation failed: {openai_error}")
        cleanup_failed_database("database.npy")
    
    # Step 3: Try to create MiniLM database as fallback
    print("\n" + "-" * 40)
    print("Attempting MiniLM database creation (fallback)...")
    print("-" * 40)
    
    mini_success, mini_error = create_mini_database()
    
    if mini_success and verify_database("database_mini.npy"):
        print("\n✅ MiniLM database created and verified successfully!")
        print("Database file: database_mini.npy")
        print("The system will use local MiniLM embeddings.")
        return True
    else:
        print(f"\n❌ MiniLM database creation failed: {mini_error}")
        cleanup_failed_database("database_mini.npy")
    
    # Step 4: All attempts failed
    print("\n" + "=" * 60)
    print("❌ CRITICAL: All database creation attempts failed!")
    print("=" * 60)
    print("\nPossible solutions:")
    print("1. Check your OpenAI API key in environment variables")
    print("2. Ensure internet connection for downloading MiniLM model")
    print("3. Check available disk space")
    print("4. Verify Python package installations")
    print("\nThe system will fall back to rule-based solutions only.")
    
    return False

def check_existing_databases():
    """
    Check what databases already exist and their status.
    """
    print("Checking existing databases...")
    
    databases = [
        ("database.npy", "OpenAI embeddings"),
        ("database_mini.npy", "MiniLM embeddings")
    ]
    
    found_valid = False
    
    for db_file, db_type in databases:
        if os.path.exists(db_file):
            if verify_database(db_file):
                print(f"✅ Valid database found: {db_file} ({db_type})")
                found_valid = True
            else:
                print(f"❌ Invalid database found: {db_file} ({db_type})")
        else:
            print(f"📁 Database not found: {db_file} ({db_type})")
    
    return found_valid

def main():
    """Main function for database creation."""
    print("RAG Database Setup Tool")
    print("=" * 60)
    
    # Check if databases already exist
    if check_existing_databases():
        response = input("\nValid database(s) found. Recreate? (y/N): ").strip().lower()
        if response not in ['y', 'yes']:
            print("Using existing database(s).")
            return
    
    # Create new database
    success = create_database()
    
    if success:
        print("\n🎉 Database setup completed successfully!")
        print("Your RAG system is ready to use.")
    else:
        print("\n⚠️  Database setup failed, but the system can still operate")
        print("using rule-based fallbacks.")

if __name__ == "__main__":
    main()