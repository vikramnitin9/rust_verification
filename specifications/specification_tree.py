# """Module to represent generated specifications."""

# from collections import deque
# from pathlib import Path

# from util import code_extraction_util
# from verification import Success, VerificationClient


# class SpecificationTree:
#     function_name: str
#     specified_function_src: str
#     repaired_specifications: list["SpecificationTree"]

#     def __init__(self, function_name: str, response_from_model: str):
#         self.function_name = function_name
#         self.specified_function_src = code_extraction_util.extract_function(response_from_model)
#         self.repaired_specifications = []

#     def get_successfully_verifying_function_src(
#         self, verifier: VerificationClient, verified_functions: set[str], path_to_src: Path
#     ) -> "SpecificationTree | None":
#         q: deque[SpecificationTree] = deque([self])
#         while q:
#             spec_tree = q.pop()
#             verification_result = verifier.verify(
#                 function_name=spec_tree.function_name,
#                 verified_functions=verified_functions,
#                 path_to_src=path_to_src,
#             )
#             if isinstance(verification_result, Success):
#                 verified_functions.add(self.function_name)
#                 return spec_tree

#             for repaired_spec_tree in spec_tree.repaired_specifications:
#                 q.append(repaired_spec_tree)
#         return None
