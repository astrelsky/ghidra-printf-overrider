//@category Functions

import java.util.Arrays;
import java.util.List;
import java.util.Optional;
import java.util.StringJoiner;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import ghidra.app.plugin.core.analysis.AutoAnalysisManager;
import ghidra.app.plugin.core.analysis.ConstantPropagationAnalyzer;
import ghidra.app.script.GhidraScript;
import ghidra.app.util.parser.FunctionSignatureParser;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.*;
import ghidra.program.model.data.DataUtilities.ClearDataMode;
import ghidra.program.model.listing.Data;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.Parameter;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.HighFunctionDBUtil;
import ghidra.program.model.symbol.RefType;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolType;
import ghidra.program.util.SymbolicPropogator;
import ghidra.util.classfinder.ClassSearcher;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

public class PrintfSigOverrider extends GhidraScript {

    private static final String PRINT_F = "printf";
    private static final String UNSUPPORTED_MESSAGE =
        "Currently only processors passing parameters via registers are supported.";

    private static final Pattern FORMAT_PATTERN =
        Pattern.compile("%\\d*([lLh]?[cdieEfgGosuxXpn%])");

    private static final String PREFIX = "int printf(";
	private static final String DELIMITER = ",";
	private static final String SUFFIX = ")";
	
	private static final FunctionSignatureParser PARSER = 
		new FunctionSignatureParser(BuiltInDataTypeManager.getDataTypeManager(), null);

	private static boolean isFunction(Symbol s) {
		return s.getSymbolType() == SymbolType.FUNCTION;
	}

	private static boolean isCall(Reference r) {
		final RefType type = r.getReferenceType();
		if (type.isCall()) {
			return !(type.isComputed() || type.isIndirect());
		}
		return false;
	}

    @Override
    public void run() throws Exception {
		Optional<Symbol> s = StreamSupport.stream(currentProgram.getSymbolTable()
										  .getSymbolIterator(PRINT_F, true)
										  .spliterator(), false)
										  .filter(PrintfSigOverrider::isFunction)
										  .findFirst();
		if (s.isPresent()) {
			final Parameter format = ((Function) s.get().getObject()).getParameter(0);
			if (format == null) {
				printerr("Unable to retrieve format parameter");
				return;
			}
			if (!format.isRegisterVariable()) {
				popup(UNSUPPORTED_MESSAGE);
				return;
			}
			List<Address> addresses = Arrays.stream(s.get().getReferences())
					.filter(PrintfSigOverrider::isCall)
					.map(Reference::getFromAddress)
					.collect(Collectors.toList());
			monitor.initialize(addresses.size());
			monitor.setMessage("Overriding printf calls");
			for (Address address : addresses) {
				monitor.checkCanceled();
				Function function = getFunctionContaining(address);
				if (function == null) {
					monitor.incrementProgress(1);
					continue;
				}
				SymbolicPropogator prop = analyzeFunction(function, monitor);
				Address nextAddr = movePastDelaySlot(address);
				SymbolicPropogator.Value value =
					prop.getRegisterValue(nextAddr, format.getRegister());
				if (value != null) {
					Address stringAddress = toAddr(value.getValue());
					if (isValidAddress(stringAddress)) {
						Data data = getDataAt(stringAddress);
						if (data == null || !data.hasStringValue()) {
							clearListing(stringAddress);
							data = DataUtilities.createData(
								currentProgram, stringAddress, StringDataType.dataType, -1, false,
								ClearDataMode.CLEAR_ALL_CONFLICT_DATA);
						}
						String msg = (String) data.getValue();
						overrideFunction(function, address, msg);
					}
				}
				monitor.incrementProgress(1);
			}
        }
	}
	
	private boolean isValidAddress(Address address) {
		final MemoryBlock block = getMemoryBlock(address);
		return block != null && !block.isExecute();
	}

    private Address movePastDelaySlot(Address addr) {
        Instruction inst = getInstructionAt(addr);
        if (inst.getDelaySlotDepth() > 0) {
            do {
                inst = inst.getNext();
            } while (inst.isInDelaySlot());
        }
        return inst.getAddress();
    }

    private void overrideFunction(Function function, Address address, String format)
        throws Exception {
            int transaction = -1; 
            if (currentProgram.getCurrentTransaction() == null) {
                transaction = currentProgram.startTransaction("Override Signature");
            }
            boolean commit = false;
            try {
				final FunctionDefinition def = getFunctionSignature(format, function);
				if (def != null) {
					HighFunctionDBUtil.writeOverride(function, address, def);
					commit = true;
				}
            }
            catch (Exception e) {
                printerr("Error overriding signature: " + e.getMessage());
            }
            finally {
                if (transaction != -1) {
                    currentProgram.endTransaction(transaction, commit);
                }
            }
	}
	
	private DataType toDataType(CharSequence match) {
		if (match.charAt(0) == 'h') {
			switch(match.charAt(1)) {
				case 'i':
				case 'd':
				case 'o':
					return ShortDataType.dataType;
				case 'u':
				case 'x':
				case 'X':
					return UnsignedShortDataType.dataType;
				default:
					printerr("Unknown specifier "+match);
					return Undefined1DataType.dataType;
			}
		} else if (match.charAt(0) == 'l') {
			switch(match.charAt(1)) {
				case 'c':
					return WideCharDataType.dataType;
				case 's':
					return PointerDataType.getPointer(WideCharDataType.dataType, -1);
				case 'i':
				case 'd':
				case 'o':
					return LongDataType.dataType;
				case 'u':
				case 'x':
				case 'X':
					return UnsignedLongDataType.dataType;
				case 'e':
				case 'E':
				case 'f':
				case 'g':
				case 'G':
					return DoubleDataType.dataType;
				default:
					printerr("Unknown specifier "+match);
					return DataType.DEFAULT;
			}
		} else if (match.charAt(0) == 'L') {
			switch(match.charAt(1)) {
				case 'e':
				case 'E':
				case 'f':
				case 'g':
				case 'G':
					return LongDoubleDataType.dataType;
				default:
					printerr("Unknown specifier "+match);
					return DataType.DEFAULT;
			}
		} else {
			switch(match.charAt(0)) {
				case 'c':
					return CharDataType.dataType;
				case 's':
					return PointerDataType.getPointer(CharDataType.dataType, -1);
				case 'i':
				case 'd':
				case 'o':
					return IntegerDataType.dataType;
				case 'u':
				case 'x':
				case 'X':
					return UnsignedIntegerDataType.dataType;
				case 'e':
				case 'E':
				case 'f':
				case 'g':
				case 'G':
					return FloatDataType.dataType;
				case 'p':
					return PointerDataType.dataType;
				default:
					printerr("Unknown specifier "+match);
					return DataType.DEFAULT;
			}
		}
	}

	private String getFmt() {
		return PointerDataType.getPointer(CharDataType.dataType, -1).toString();
	}

	private static String getSpecifier(MatchResult r) {
		return r.group(1);
	}

	private static String getDeclaration(DataType dt) {
		if (dt instanceof AbstractIntegerDataType) {
			return ((AbstractIntegerDataType) dt).getCDeclaration();
		}
		return dt.toString();
	}

	private FunctionDefinition getFunctionSignature(String format, Function function)
		throws Exception {
			Matcher matcher = FORMAT_PATTERN.matcher(format);
			final StringJoiner joiner = new StringJoiner(DELIMITER, PREFIX, SUFFIX).add(getFmt());
			matcher.results()
				.map(PrintfSigOverrider::getSpecifier)
				.map(this::toDataType)
				.map(PrintfSigOverrider::getDeclaration)
				.forEach(joiner::add);
			return PARSER.parse(function.getSignature(), joiner.toString());
    }

    // These should be in a Util class somewhere!

    public static ConstantPropagationAnalyzer getConstantAnalyzer(Program program) {
        AutoAnalysisManager mgr = AutoAnalysisManager.getAnalysisManager(program);
        List<ConstantPropagationAnalyzer> analyzers = 
            ClassSearcher.getInstances(ConstantPropagationAnalyzer.class);
        for (ConstantPropagationAnalyzer analyzer : analyzers) {
            if (analyzer.canAnalyze(program)) {
                return (ConstantPropagationAnalyzer) mgr.getAnalyzer(analyzer.getName());
            }
        }
        return null;
    }

    public static SymbolicPropogator analyzeFunction(Function function, TaskMonitor monitor)
        throws CancelledException {
            Program program = function.getProgram();
            ConstantPropagationAnalyzer analyzer = getConstantAnalyzer(program);
            SymbolicPropogator symEval = new SymbolicPropogator(program);
            symEval.setParamRefCheck(true);
            symEval.setReturnRefCheck(true);
            symEval.setStoredRefCheck(true);
            analyzer.flowConstants(program, function.getEntryPoint(), function.getBody(),
                                   symEval, monitor);
            return symEval;
	}

}
