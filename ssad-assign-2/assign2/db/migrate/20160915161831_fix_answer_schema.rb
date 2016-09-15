class FixAnswerSchema < ActiveRecord::Migration[5.0]
  def change
    drop_table :answers

    create_table :answers do |t|
      t.string :answer
      t.integer :question_id
      t.timestamps
      end
  end
end
