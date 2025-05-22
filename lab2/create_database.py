import os
import sys

sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from src.embedding_db import VectorDB
from src.embedding_models import OpenAIEmbeddingModel, MiniEmbeddingModel

def create_database():
    """
    Create the embedding database for RAG.
    """
    print("Creating embedding database...")
    
    # Ensure documents directory exists
    os.makedirs("documents", exist_ok=True)
    
    # Check if there are any files in the documents directory
    document_files = [f for f in os.listdir("documents") if f.endswith('.txt')]
    if not document_files:
        print("Warning: No text files found in documents directory. Creating sample file...")
        with open("documents/sample.txt", "w") as f:
            f.write("This is a sample document for testing the RAG system. <EOC>\n")
            f.write("Lean 4 is a programming language and theorem prover. <EOC>\n")
    
    try:
        # Try with OpenAI embeddings first
        print("Using OpenAI embedding model")
        embedding_model = OpenAIEmbeddingModel()
        vector_db = VectorDB(
            directory="documents",
            vector_file="database.npy",
            embedding_model=embedding_model
        )
        print("Database created successfully with OpenAI embeddings!")
    except Exception as e:
        print(f"Error creating database with OpenAI embeddings: {e}")
        print("Falling back to MiniLM embedding model")
        
        try:
            # Fallback to MiniLM embeddings
            embedding_model = MiniEmbeddingModel()
            vector_db = VectorDB(
                directory="documents",
                vector_file="database_mini.npy",
                embedding_model=embedding_model
            )
            print("Database created successfully with MiniLM embeddings!")
        except Exception as e:
            print(f"Error creating database with MiniLM embeddings: {e}")
            print("Please check your environment and try again.")

if __name__ == "__main__":
    create_database()