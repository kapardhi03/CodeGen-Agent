from openai import OpenAI
import os
import time
from typing import List, Dict, Optional

class LLM_Agent:
    def __init__(self, model: str = "gpt-4o", max_retries: int = 3, timeout: int = 60):
        """
        Initializes the OpenAI client with the selected model.

        Args:
            model (str): Either "gpt-4o" or "o3-mini".
            max_retries (int): Maximum number of retry attempts for API calls.
            timeout (int): Timeout for API calls in seconds.
        """
        self.model = model
        self.max_retries = max_retries
        self.timeout = timeout
        
        # Check if API key is available
        self.api_key = os.getenv("OPENAI_API_KEY")
        if not self.api_key:
            print("Warning: OPENAI_API_KEY not found. Agent will not be functional.")
            self.client = None
        else:
            self.client = OpenAI(api_key=self.api_key)
        
    def get_response(self, messages: List[Dict[str, str]]) -> str:
        """
        Sends a prompt to the OpenAI model and returns the response with retry logic.

        Args:
            messages (List[Dict]): The conversation messages.

        Returns:
            str: The model's response.

        Raises:
            Exception: If API is unavailable or all retries failed.
        """
        if not self.client:
            raise Exception("OpenAI client not initialized. Check API key.")
        
        last_error = None
        
        for attempt in range(self.max_retries):
            try:
                print(f"Attempting API call (attempt {attempt + 1}/{self.max_retries})...")
                
                completion = self.client.chat.completions.create(
                    model=self.model,
                    messages=messages,
                    timeout=self.timeout
                )
                
                response = completion.choices[0].message.content
                print(f"API call successful on attempt {attempt + 1}")
                return response
                
            except Exception as e:
                last_error = e
                print(f"Attempt {attempt + 1} failed: {str(e)}")
                
                if attempt < self.max_retries - 1:
                    # Exponential backoff
                    sleep_time = (2 ** attempt) * 1
                    print(f"Retrying in {sleep_time} seconds...")
                    time.sleep(sleep_time)
                else:
                    print("All retry attempts failed.")
        
        # If we get here, all retries failed
        raise Exception(f"API call failed after {self.max_retries} attempts. Last error: {str(last_error)}")
    
    def is_available(self) -> bool:
        """
        Check if the agent is available (has valid API key and can make calls).
        
        Returns:
            bool: True if agent is available, False otherwise.
        """
        if not self.client:
            return False
        
        try:
            # Make a simple test call
            test_messages = [
                {"role": "system", "content": "You are a helpful assistant."},
                {"role": "user", "content": "Say 'test' if you can hear me."}
            ]
            
            completion = self.client.chat.completions.create(
                model=self.model,
                messages=test_messages,
                max_tokens=10,
                timeout=10
            )
            
            return True
            
        except Exception as e:
            print(f"Agent availability check failed: {e}")
            return False

class Reasoning_Agent(LLM_Agent):
    def __init__(self, model: str = "o3-mini", max_retries: int = 3, timeout: int = 120):
        """
        Initializes the reasoning agent with o3-mini model (or fallback).

        Args:
            model (str): Reasoning model to use.
            max_retries (int): Maximum number of retry attempts for API calls.
            timeout (int): Timeout for API calls in seconds (longer for reasoning).
        """
        super().__init__(model, max_retries, timeout)
    
    def get_response(self, messages: List[Dict[str, str]]) -> str:
        """
        Get response from reasoning model with additional reasoning prompting.
        
        Args:
            messages (List[Dict]): The conversation messages.
            
        Returns:
            str: The model's response with reasoning.
        """
        # Enhance the system message for better reasoning
        enhanced_messages = messages.copy()
        
        if enhanced_messages and enhanced_messages[0]["role"] == "system":
            enhanced_messages[0]["content"] += " Think step by step and provide detailed reasoning."
        else:
            enhanced_messages.insert(0, {
                "role": "system", 
                "content": "You are an expert reasoning assistant. Think step by step and provide detailed analysis."
            })
        
        return super().get_response(enhanced_messages)

class LocalAgent:
    """
    Fallback agent that provides rule-based responses when API agents are unavailable.
    """
    
    def __init__(self):
        self.available = True
    
    def get_response(self, messages: List[Dict[str, str]]) -> str:
        """
        Provide rule-based responses for common queries.
        
        Args:
            messages (List[Dict]): The conversation messages.
            
        Returns:
            str: A rule-based response.
        """
        # Extract the main content from messages
        user_content = ""
        for msg in messages:
            if msg["role"] == "user":
                user_content += msg["content"] + " "
        
        user_content = user_content.lower()
        
        # Rule-based responses for common patterns
        if "proof" in user_content and "error" in user_content:
            return """The proof has an error. Common fixes:
            1. Use 'rfl' for simple equality proofs
            2. Use 'simp' for basic simplification
            3. Use 'exact' followed by a proof term
            4. Check that all variables are properly bound
            5. Ensure the proof structure matches the goal"""
        
        elif "implementation" in user_content and "error" in user_content:
            return """The implementation has an error. Common fixes:
            1. Check syntax and parentheses
            2. Verify type annotations match expected types
            3. Ensure all variables are defined
            4. Check that function calls have correct arguments
            5. Verify array/list operations use correct methods"""
        
        elif "plan" in user_content:
            return """Implementation Plan:
            1. Analyze the problem requirements carefully
            2. Identify the input and output types
            3. Break down the problem into smaller steps
            4. Implement using simple, direct approaches
            5. Use standard Lean 4 libraries when possible
            
            Proof Strategy:
            1. Start with the specification
            2. Use 'unfold' to expand definitions
            3. Apply appropriate tactics (rfl, simp, exact)
            4. Build proofs step by step
            5. Use constructors for complex propositions"""
        
        elif "generate" in user_content or "implement" in user_content:
            return """CODE:
            -- Implementation depends on specific problem
            -- Use direct, simple approaches
            -- Follow Lean 4 syntax carefully
            
            PROOF:
            -- Start with unfold
            -- Use appropriate tactics
            -- Build step by step"""
        
        else:
            return """I can provide basic guidance, but detailed analysis requires more context. 
            Common approaches:
            - For implementations: use simple, direct code
            - For proofs: start with 'unfold' and use basic tactics
            - Check syntax and types carefully"""
    
    def is_available(self) -> bool:
        """Local agent is always available."""
        return True

def create_agent_with_fallback(primary_model: str = "gpt-4o", agent_type: str = "llm") -> LLM_Agent:
    """
    Create an agent with automatic fallback to local agent if API is unavailable.
    
    Args:
        primary_model (str): The primary model to try.
        agent_type (str): Type of agent ("llm" or "reasoning").
        
    Returns:
        An agent instance (either API-based or local fallback).
    """
    try:
        if agent_type == "reasoning":
            agent = Reasoning_Agent(primary_model)
        else:
            agent = LLM_Agent(primary_model)
        
        # Test if agent is available
        if agent.is_available():
            print(f"Successfully created {agent_type} agent with {primary_model}")
            return agent
        else:
            print(f"API agent unavailable, using local fallback")
            return LocalAgent()
            
    except Exception as e:
        print(f"Failed to create API agent: {e}")
        print("Using local fallback agent")
        return LocalAgent()

# Example usage and testing
if __name__ == "__main__":
    print("Testing agent creation and availability...")
    
    # Test LLM Agent
    print("\n=== Testing LLM Agent ===")
    llm_agent = create_agent_with_fallback("gpt-4o", "llm")
    print(f"LLM Agent available: {llm_agent.is_available()}")
    
    # Test Reasoning Agent  
    print("\n=== Testing Reasoning Agent ===")
    reasoning_agent = create_agent_with_fallback("o3-mini", "reasoning")
    print(f"Reasoning Agent available: {reasoning_agent.is_available()}")
    
    # Test local agent response
    print("\n=== Testing Local Agent Response ===")
    local_agent = LocalAgent()
    test_messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": "I have a proof error in my Lean code. Can you help?"}
    ]
    response = local_agent.get_response(test_messages)
    print(f"Local agent response: {response[:100]}...")
    
    print("\nAgent testing complete.")