package Intercept.HelloWorldAgent;
import soot.Unit;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class ConditionTag implements Tag {
		public static final String NAME = "ConditionTag";
		private Unit ifStmt;
		private boolean branch;

		public ConditionTag(Unit ifStmt, boolean branch) {
			this.ifStmt = ifStmt;
			this.branch = branch;
		}

		@Override
		public String getName() {
			return NAME;
		}

		@Override
		public byte[] getValue() throws AttributeValueException {
			return ifStmt.toString().getBytes();
		}

		public Unit getIfStmt() {
			return this.ifStmt;
		}

		public boolean getBranch() {
			return this.branch;
		}
	}